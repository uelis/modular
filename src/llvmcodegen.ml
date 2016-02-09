open Core_kernel.Std

let context = Llvm.global_context ()
let builder = Llvm.builder context

(** Position builder at start of block *)
let position_at_start block builder =
  let block_begin = Llvm.instr_begin block in
  Llvm.position_builder block_begin builder

(** Number of bits needed to store [i] different values. *)
let rec log i =
  if i > 1 then 1 + (log (i - i/2)) else 0

(** Representation of LLVM types suitable for use as keys in a map. *)
module Lltype: sig

  type t =
    | Integer of int
    | Pointer (* void pointer *)
    [@@deriving sexp]

  module Map: Map.S with type Key.t = t

  val int_type: t
  val to_lltype: t -> Llvm.lltype
end
= struct

  module T = struct
    type t =
      | Integer of int
      | Pointer
    [@@deriving sexp]

    let compare (x: t) (y: t) =
      match x, y with
      | Pointer, Pointer -> 0
      | Integer i, Integer j -> Int.compare i j
      | Pointer, Integer _ -> 1
      | Integer _, Pointer -> -1
  end
  include T
  module Map = Map.Make(T)

  let int_type = Integer !Opts.int_size

  let to_lltype (x: t) =
    match x with
    | Integer 0 ->
      Llvm.integer_type context 1
    | Integer i ->
      Llvm.integer_type context i
    | Pointer -> Llvm.pointer_type (Llvm.i8_type context)

end

(** A profile is a finite map from llvm types to numbers.
    Below, ssa values are encoded as vectors of llvm values
    of different type.The profile of a vector explains how many
    values of each type it contains.

    The following module enforces the invariant that
    keys are all > 0 and if a key has a value then this
    value is > 0.
*)
module Profile: sig

  type t

  (* The empty profile. *)
  val null : t

  (* Profile of a vector containing a single value of the given type.*)
  val singleton : Lltype.t -> t

  (* Profile of a vector containing n values of the given type. *)
  val ntimes : Lltype.t -> int -> t

  (* Profile of the values from both given profiles together. *)
  val add : t -> t -> t

  (** To each [a: Basetype.t] we assign a profile [of_basetype a].
      The values of type [a] will be represented by vectors of this profile. *)
  val of_basetype: Basetype.t -> t

  val equal : t -> t -> bool
  val find : t -> Lltype.t -> int option
  val mapi : t -> f:(key:Lltype.t -> data:int -> 'a) -> 'a Lltype.Map.t
  val fold_right : t -> init:'a -> f:(key:Lltype.t -> data:int -> 'a -> 'a) -> 'a

end
= struct

  type t = int Lltype.Map.t

  let null = Lltype.Map.empty
  let singleton i = Lltype.Map.singleton i 1
  let ntimes i n =
    if n <=0 then failwith "ntimes argument";
    Lltype.Map.singleton i n

  let merge (p1: t) (p2: t) ~f:(f:int -> int -> int) : t =
    Lltype.Map.merge p1 p2
      ~f:(fun ~key:_ -> function
        | `Both(m, n) -> Some (f m n)
        | `Left(n) | `Right(n) -> Some n)

  let add = merge ~f:(+)
  let max = merge ~f:(max)

  (*
  let print p =
    Lltype.Map.iter p ~f:(fun ~key:i ~data:n -> Printf.printf "%i->%i, " i n);
    Printf.printf "\n"
  *)

  let of_basetype (a: Basetype.t) : t =
    let rec a_s a =
      let open Basetype in
      match case a with
      | Var -> null
      | Sgn sa ->
        begin
          match sa with
          | ZeroB | UnitB -> null
          | IntB -> singleton Lltype.int_type
          | BoxB _ -> singleton Lltype.Pointer
          | PairB(a1, a2) -> add (a_s a1) (a_s a2)
          | DataB(id, ps) ->
            begin
              let cs = Basetype.Data.constructor_types id ps in
              let n = List.length cs in
              let mx = List.fold_right cs ~f:(fun c mx -> max (a_s c) mx)
                         ~init:Lltype.Map.empty in
              if n = 1 || Basetype.Data.is_discriminated id = false then
                mx
              else
                let i = Lltype.Integer (log n) in
                let ni = Lltype.Map.find mx i |> Option.value ~default:0 in
                Lltype.Map.add mx ~key:i ~data:(ni + 1)
            end
        end
    in a_s a

  let equal = Lltype.Map.equal (=)
  let find = Lltype.Map.find
  let mapi = Lltype.Map.mapi
  let fold_right = Lltype.Map.fold_right
end

(** Encapsulate vectors of values of varying bit width. *)
module Mixedvector :
sig
  type t

  (** Profile of vector *)
  val to_profile : t -> Profile.t

  (** Empty vector *)
  val null : t

  (** Singleton vector containing a single value of
      given bit width. The call [singleton n v] produces
      a vector with profile [n -> 1]. *)
  val singleton : Lltype.t -> Llvm.llvalue -> t

  (** Join two vectors. For each bit width, the vectors are concatenated in
      order. *)
  val concatenate : t -> t -> t

  (** Takes the prefix vector specified by profile and returns also the rest. *)
  val takedrop : t -> Profile.t -> t * t

  (** Take prefix or fill up with undefs so that value fits the profile. *)
  val coerce : t -> Profile.t -> t

  (** Extract the value from a singleton vector. *)
  val llvalue_of_singleton : t -> Llvm.llvalue

  (** Extract the list of all values for a given key. *)
  val llvalues_at_key: t -> Lltype.t -> Llvm.llvalue list

  (** Build a vector of singleton phi nodes for the llvalues
      stored in the given vector. *)
  val build_phi:  t * Llvm.llbasicblock -> Llvm.llbuilder -> t

  (** Add an incoming vector to vector of phi nodes. *)
  val add_incoming: t * Llvm.llbasicblock -> t -> unit

  (** Returns an LLVM type that can store a vector of the given profile. *)
  val packing_type: Profile.t -> Llvm.lltype

  (** Encodes a vector into its packing type. *)
  val pack : t -> Llvm.llvalue

  (** Decodes a vector from its packing type. *)
  val unpack : Profile.t -> Llvm.llvalue -> t
end =
struct

  type t = { bits : (Llvm.llvalue list) Lltype.Map.t }

  let null = { bits = Lltype.Map.empty }
  let singleton i v = { bits = Lltype.Map.singleton i [v] }

  let concatenate v w =
    { bits =
        Lltype.Map.merge v.bits w.bits
          ~f:(fun ~key:_ -> function
            | `Both(vn, wn) -> Some (vn @ wn)
            | `Left(vn) | `Right(vn) -> Some vn)
    }

  (* precond: v enthält mindestens so viele Werte, wie vom Profil angegeben *)
  let takedrop v profile =
    { bits = Profile.mapi profile
               ~f:(fun ~key:n ~data:ln ->
                 let vn = Lltype.Map.find v.bits n
                          |> Option.value ~default:[] in
                 assert (ln <= List.length vn);
                 let vn1, _ = List.split_n vn ln in
                 vn1) },
    { bits = Lltype.Map.fold v.bits
               ~f:(fun ~key:n ~data:vn v2 ->
                 let ln = Profile.find profile n
                          |> Option.value ~default:0 in
                 let _, vn2 = List.split_n vn ln in
                 if (vn2 <> []) then
                   Lltype.Map.add v2 ~key:n ~data:vn2
                 else v2)
               ~init:Lltype.Map.empty}


  let coerce v profile =
    let rec fill_cut i l n =
      if n = 0 then [] else
        match l with
        | [] ->
          Llvm.undef (Lltype.to_lltype i) :: (fill_cut i [] (n-1))
        | x::xs -> x :: (fill_cut i xs (n-1)) in
    { bits = Profile.mapi profile
               ~f:(fun ~key:i ~data:n ->
                 let vi = Lltype.Map.find v.bits i
                          |> Option.value ~default:[] in
                 fill_cut i vi n)}

  let llvalue_of_singleton v =
    List.hd_exn (snd (Lltype.Map.min_elt_exn v.bits))

  let llvalues_at_key (x: t) (k: Lltype.t) =
    Lltype.Map.find x.bits k |> Option.value ~default:[]

  let to_profile (x: t) : Profile.t =
    Lltype.Map.fold x.bits
      ~f:(fun ~key:k ~data:xs m ->
        Profile.add (Profile.ntimes k (List.length xs)) m)
      ~init:Profile.null

  let build_phi (x, srcblock) builder =
    let phis bits
      = List.map bits
          ~f:(fun x -> Llvm.build_phi [(x, srcblock)] "x" builder) in
    { bits = Lltype.Map.map x.bits ~f:(fun bits -> phis bits) }

  let add_incoming (y, blocky) x =
    let add_incoming_n (y, blocky) x =
      List.iter2_exn y x
        ~f:(fun yi xi -> Llvm.add_incoming (yi, blocky) xi) in
    List.iter (Lltype.Map.keys y.bits)
      ~f:(fun n -> add_incoming_n
                     (Lltype.Map.find_exn y.bits n, blocky)
                     (Lltype.Map.find_exn x.bits n))

  let packing_type profile =
    let struct_members =
      Profile.fold_right profile (* ascending order is guaranteed *)
        ~f:(fun ~key:i ~data:n args ->
          args @ (List.init n ~f:(fun _ -> Lltype.to_lltype i)))
        ~init:[] in
    let tags_and_members =
      [ Llvm.integer_type context 64 ]   (* tag *)
      @ struct_members in
    Llvm.packed_struct_type context (Array.of_list tags_and_members)

  let pack x =
    let struct_type = to_profile x |> packing_type in
    let values =
      Lltype.Map.fold_right x.bits
        ~f:(fun ~key:_ ~data:xs vals -> vals @ xs)
        ~init:[] in
    let number_of_ptrs =
      match Profile.find (to_profile x) Lltype.Pointer with
      | Some n -> n
      | None -> 0 in
    let tag =
        let i64 = Llvm.integer_type context 64 in
        let ep = Llvm.build_gep
            (Llvm.const_null (Llvm.pointer_type struct_type))
            [| Llvm.const_int i64 1 |]
            "ep" builder in
        let size = Llvm.build_ptrtoint ep i64 "size" builder in
        let nptrs = Llvm.const_int i64 number_of_ptrs in
        let nofwd = Llvm.const_int i64 1 in
        let t1 = Llvm.build_shl size (Llvm.const_int i64 32) "size" builder in
        let t2 = Llvm.build_shl nptrs (Llvm.const_int i64 1) "nnptrs" builder in
        let t3 = Llvm.build_add t1 t2 "t3" builder in
        Llvm.build_add t3 nofwd "tag" builder in
    let tags_and_values = tag :: values in
    List.foldi tags_and_values
         ~f:(fun i s v -> Llvm.build_insertvalue s v i "pack" builder)
         ~init: (Llvm.undef struct_type)

  let unpack profile v =
    let bits, _ =
      Profile.fold_right profile
        ~f:(fun ~key:k ~data:n (bits, pos)->
          let bitsn =
            List.init n
              ~f:(fun i -> Llvm.build_extractvalue v (pos + i)
                             "unpack" builder) in
          Lltype.Map.add bits ~key:k ~data:bitsn,
          pos + n)
        ~init:(Lltype.Map.empty, 1) (* first item is the tag *)
    in {bits = bits}
end

type encoded_value = Mixedvector.t

(** Assertion to state tenc encodes a value of type a. *)
let assert_type tenc a =
  (*  assert (List.length tenc.payload = payload_size a); *)
  assert (Profile.equal (Profile.of_basetype a) (Mixedvector.to_profile tenc))

(** Truncate or fill with undefs the vectors in [enc], so
    that it becomes a value of type [a]. *)
let build_truncate_extend (enc : encoded_value) (a : Basetype.t)
  : encoded_value =
  (*  let a_payload_size = payload_size a in *)
  let a_attrib_bitlen = Profile.of_basetype a in
  Mixedvector.coerce enc a_attrib_bitlen

let packing_type (a: Basetype.t) : Llvm.lltype =
  Mixedvector.packing_type (Profile.of_basetype a)

let pack_encoded_value (enc: encoded_value) (a: Basetype.t): Llvm.llvalue =
  assert_type enc a;
  Mixedvector.pack enc

let unpack_encoded_value (packed_enc: Llvm.llvalue) (a: Basetype.t)
  : encoded_value =
  let len_a = Profile.of_basetype a in
  Mixedvector.unpack len_a packed_enc

let int_lltype = Lltype.to_lltype Lltype.int_type

(** Encoding of values *)
let rec build_value
      (the_module : Llvm.llmodule)
      (ctx: (Ident.t * encoded_value) list)
      (t: Ssa.value) : encoded_value =
  match t with
  | Ssa.Var(x) ->
    List.Assoc.find_exn ctx x
  | Ssa.IntConst(i) ->
    let vali = Llvm.const_int (int_lltype) i in
    Mixedvector.singleton Lltype.int_type vali
  | Ssa.Unit ->
    Mixedvector.null
  | Ssa.Pair(t1, t2) ->
    let t1enc = build_value the_module ctx t1 in
    let t2enc = build_value the_module ctx t2 in
    Mixedvector.concatenate t1enc t2enc
  | Ssa.In((id, _, t), a) when
      Basetype.Data.constructor_count id = 1 ||
      Basetype.Data.is_discriminated id = false ->
    let tenc = build_value the_module ctx t in
    build_truncate_extend tenc a
  | Ssa.In((id, i, t), a) ->
    let n = Basetype.Data.constructor_count id in
    let tenc = build_value the_module ctx t in
    let branch = Llvm.const_int (Llvm.integer_type context (log n)) i in
    let denc = Mixedvector.concatenate
                 (Mixedvector.singleton (Lltype.Integer (log n)) branch)
                 tenc in
    build_truncate_extend denc a
  | Ssa.Fst(t, a, b) ->
    let tenc = build_value the_module ctx t in
    let len_aa = Profile.of_basetype a in
    let t1a, t2a = Mixedvector.takedrop tenc len_aa in
    assert (Profile.equal (Profile.of_basetype a) (Mixedvector.to_profile t1a));
    assert (Profile.equal (Profile.of_basetype b) (Mixedvector.to_profile t2a));
    t1a
  | Ssa.Snd(t, a, b) ->
    let tenc = build_value the_module ctx t in
    let len_aa = Profile.of_basetype a in
    let t1a, t2a = Mixedvector.takedrop tenc len_aa in
    assert (Profile.equal (Profile.of_basetype a) (Mixedvector.to_profile t1a));
    assert (Profile.equal (Profile.of_basetype b) (Mixedvector.to_profile t2a));
    t2a
  | Ssa.Select(t, (id, params), i)
    when Basetype.Data.is_discriminated id = false ->
    let tenc = build_value the_module ctx t in
    let case_types = Basetype.Data.constructor_types id params in
    let ai = List.nth_exn case_types i in
    build_truncate_extend tenc ai
  | Ssa.Select(t, (id, params), i) ->
    let tenc = build_value the_module ctx t in
    let n = Basetype.Data.constructor_count id in
    if n = 1 then
      build_value the_module ctx t
    else
      begin
        let yenc =
          let _, ya =
            Mixedvector.takedrop tenc (Profile.singleton (Lltype.Integer (log n))) in
          ya in
        let case_types = Basetype.Data.constructor_types id params in
        assert (i < List.length case_types);
        let ai = List.nth_exn case_types i in
        build_truncate_extend yenc ai
      end
  | Ssa.Undef(a) ->
    build_truncate_extend Mixedvector.null a

(** Encoding of terms *)
let build_term
    (the_module : Llvm.llmodule)
    (func : Llvm.llvalue)
    (ctx: (Ident.t * encoded_value) list)
    (t: Ssa.term) : encoded_value =
  match t with
  | Ssa.Val(v) -> build_value the_module ctx v
  | Ssa.Const(Ssa.Cpush(a), v) ->
    let salloc =
      match Llvm.lookup_function "salloc" the_module with
      | Some salloc -> salloc
      | None -> assert false in
    let a_struct = packing_type a in
    let mem_i8ptr = Llvm.build_call salloc
        [| Llvm.size_of a_struct |]
        "memi8" builder in
    let mem_ptr = Llvm.build_bitcast mem_i8ptr (Llvm.pointer_type a_struct)
        "memstruct" builder in
    let venc = build_value the_module ctx v in
    let v_packed = pack_encoded_value (build_truncate_extend venc a) a in
    ignore (Llvm.build_store v_packed mem_ptr builder);
    Mixedvector.null
  | Ssa.Const(Ssa.Cpop(a), _) ->
    let spop =
      match Llvm.lookup_function "spop" the_module with
      | Some spop -> spop
      | None -> assert false in
    let a_struct = packing_type a in
    let mem_i8ptr = Llvm.build_call spop [| Llvm.size_of a_struct |]
        "memi8" builder in
    let mem_ptr = Llvm.build_bitcast mem_i8ptr (Llvm.pointer_type a_struct)
        "memstruct" builder in
    let lstruct = Llvm.build_load mem_ptr "lstruct" builder in
    unpack_encoded_value lstruct a
  | Ssa.Const(Ssa.Cprint(s), _) ->
    let str = Llvm.build_global_string s "s" builder in
    let strptr = Llvm.build_in_bounds_gep str
        [| Llvm.const_null int_lltype; Llvm.const_null int_lltype |]
        "strptr" builder in
    let strptrint = Llvm.build_ptrtoint strptr int_lltype "strptrint" builder in
    let i8a = Llvm.pointer_type (Llvm.i8_type context) in
    let formatstr = Llvm.build_global_string "%s" "format" builder in
    let formatstrptr = Llvm.build_in_bounds_gep formatstr
        [| Llvm.const_null int_lltype; Llvm.const_null int_lltype |]
        "forrmatptr" builder in
    let printftype = Llvm.function_type (int_lltype)
        [| i8a; int_lltype |] in
    let printf = Llvm.declare_function "printf" printftype the_module in
    let args = Array.of_list [formatstrptr; strptrint] in
    ignore (Llvm.build_call printf args "i" builder);
    Mixedvector.null
  | Ssa.Const(Ssa.Ccall(e, a, b), v) ->
    let a_struct = packing_type a in
    let b_struct = packing_type b in
    let etype = Llvm.function_type b_struct (Array.of_list [a_struct]) in
    let efunc = Llvm.declare_function e etype the_module in
    let venc = build_value the_module ctx v in
    let v_packed = pack_encoded_value (build_truncate_extend venc a) a in
    let args = Array.of_list [v_packed] in
    let res_packed = Llvm.build_call efunc args e builder in
    unpack_encoded_value res_packed b
  | Ssa.Const(Ssa.Cintadd as const, arg)
  | Ssa.Const(Ssa.Cintsub as const, arg)
  | Ssa.Const(Ssa.Cintmul as const, arg)
  | Ssa.Const(Ssa.Cintdiv as const, arg)
  | Ssa.Const(Ssa.Cinteq as const, arg)
  | Ssa.Const(Ssa.Cintlt as const, arg)
  | Ssa.Const(Ssa.Cintslt as const, arg)
  | Ssa.Const(Ssa.Cintshl as const, arg)
  | Ssa.Const(Ssa.Cintshr as const, arg)
  | Ssa.Const(Ssa.Cintsar as const, arg)
  | Ssa.Const(Ssa.Cintand as const, arg)
  | Ssa.Const(Ssa.Cintor as const, arg)
  | Ssa.Const(Ssa.Cintxor as const, arg)
  | Ssa.Const(Ssa.Cintprint as const, arg)
  | Ssa.Const(Ssa.Cgcalloc _ as const, arg)
  | Ssa.Const(Ssa.Calloc _ as const, arg)
  | Ssa.Const(Ssa.Cfree _ as const, arg)
  | Ssa.Const(Ssa.Cload _ as const, arg)
  | Ssa.Const(Ssa.Cstore _ as const, arg) ->
    begin
      let argenc = build_value the_module ctx arg in
      let intargs = Mixedvector.llvalues_at_key argenc Lltype.int_type in
      let ptrargs = Mixedvector.llvalues_at_key argenc Lltype.Pointer in
      match const, intargs, ptrargs with
      | Ssa.Cintadd, [x; y], [] ->
        Mixedvector.singleton Lltype.int_type (Llvm.build_add x y "add" builder)
      | Ssa.Cintadd, _, _ -> failwith "internal: wrong argument to intadd"
      | Ssa.Cintsub, [x; y], [] ->
        Mixedvector.singleton Lltype.int_type (Llvm.build_sub x y "sub" builder)
      | Ssa.Cintsub, _, _ -> failwith "internal: wrong argument to intsub"
      | Ssa.Cintmul, [x; y], [] ->
        Mixedvector.singleton Lltype.int_type (Llvm.build_mul x y "mul" builder)
      | Ssa.Cintmul, _, _ -> failwith "internal: wrong argument to intmul"
      | Ssa.Cintdiv, [x; y], [] ->
        Mixedvector.singleton Lltype.int_type (Llvm.build_sdiv x y "sdiv" builder)
      | Ssa.Cintdiv, _, _ -> failwith "internal: wrong argument to intdiv"
      | Ssa.Cinteq, [x; y], [] ->
        Mixedvector.singleton (Lltype.Integer 1)
          (Llvm.build_icmp Llvm.Icmp.Ne x y "eq" builder)
      | Ssa.Cinteq, _, _ -> failwith "internal: wrong argument to inteq"
      | Ssa.Cintlt, [x; y], [] ->
        Mixedvector.singleton (Lltype.Integer 1)
          (Llvm.build_icmp Llvm.Icmp.Uge x y "lt" builder )
      | Ssa.Cintlt, _, _ -> failwith "internal: wrong argument to intslt"
      | Ssa.Cintslt, [x; y], [] ->
        Mixedvector.singleton (Lltype.Integer 1)
          (Llvm.build_icmp Llvm.Icmp.Sge x y "slt" builder )
      | Ssa.Cintslt, _, _ -> failwith "internal: wrong argument to intslt"
      | Ssa.Cintshl, [x; y], [] ->
        Mixedvector.singleton Lltype.int_type (Llvm.build_shl x y "shl" builder)
      | Ssa.Cintshl, _, _ -> failwith "internal: wrong argument to intshl"
      | Ssa.Cintshr, [x; y], [] ->
        Mixedvector.singleton Lltype.int_type (Llvm.build_lshr x y "shr" builder)
      | Ssa.Cintshr, _, _ -> failwith "internal: wrong argument to intshr"
      | Ssa.Cintsar, [x; y], [] ->
        Mixedvector.singleton Lltype.int_type (Llvm.build_ashr x y "sar" builder)
      | Ssa.Cintsar, _, _ -> failwith "internal: wrong argument to intsar"
      | Ssa.Cintand, [x; y], [] ->
        Mixedvector.singleton Lltype.int_type (Llvm.build_and x y "and" builder)
      | Ssa.Cintand, _, _ -> failwith "internal: wrong argument to intand"
      | Ssa.Cintor, [x; y], [] ->
        Mixedvector.singleton Lltype.int_type (Llvm.build_or x y "or" builder)
      | Ssa.Cintor, _, _ -> failwith "internal: wrong argument to intor"
      | Ssa.Cintxor, [x; y], [] ->
        Mixedvector.singleton Lltype.int_type (Llvm.build_xor x y "xor" builder)
      | Ssa.Cintxor, _, _ -> failwith "internal: wrong argument to intxor"
      | Ssa.Cintprint, [x], [] ->
        let i8a = Llvm.pointer_type (Llvm.i8_type context) in
        let formatstr = Llvm.build_global_string "%i" "format" builder in
        let formatstrptr = Llvm.build_in_bounds_gep formatstr
            [| Llvm.const_null int_lltype; Llvm.const_null int_lltype |]
            "forrmatptr" builder in
        let printftype = Llvm.function_type (int_lltype)
            [| i8a; int_lltype |] in
        let printf = Llvm.declare_function "printf" printftype the_module in
        let args = [| formatstrptr; x |] in
        ignore (Llvm.build_call printf args "i" builder);
        Mixedvector.null
      | Ssa.Cintprint, _, _ -> failwith "internal: wrong argument to intprint"
      | Ssa.Cgcalloc(a), _, _ ->
        let malloc =
          match Llvm.lookup_function "gc_alloc" the_module with
          | Some malloc -> malloc
          | None -> assert false in
        let a_struct = packing_type a in
        let addr = Llvm.build_call malloc
            [| Llvm.size_of a_struct |]
            "addr" builder in
        let oom_block = Llvm.append_block context "collect" func in
        let ok_block = Llvm.append_block context "alloc_ok" func in
        let nullptr = Llvm.const_null (Lltype.to_lltype Lltype.Pointer) in
        let oom = Llvm.build_icmp (Llvm.Icmp.Eq) addr nullptr "oom" builder in
        ignore (Llvm.build_cond_br oom oom_block ok_block builder);
        Llvm.position_at_end oom_block builder;
        let local_roots =
          let roots e =
            Mixedvector.llvalues_at_key e Lltype.Pointer in
          List.concat_map ctx ~f:(fun (_, e) -> roots e) in
        let collect =
          match Llvm.lookup_function "gc_collect" the_module with
          | Some collect -> collect
          | None -> assert false in
        if (local_roots <> []) then
          ignore (Llvm.build_call collect
                    (Array.of_list (Llvm.const_int (Llvm.i64_type context) (List.length local_roots) ::
                                    local_roots))
                    "" builder);
        ignore (Llvm.build_br ok_block builder);
        Llvm.position_at_end ok_block builder;
        Mixedvector.singleton Lltype.Pointer addr
      | Ssa.Calloc(a), _, _ ->
        let malloc =
          match Llvm.lookup_function "malloc" the_module with
          | Some malloc -> malloc
          | None -> assert false in
        let a_struct = packing_type a in
        let addr = Llvm.build_call malloc
            [| Llvm.size_of a_struct |]
            "addr" builder in
        Mixedvector.singleton Lltype.Pointer addr
      | Ssa.Cfree _, [], [addr] ->
        let free =
          match Llvm.lookup_function "free" the_module with
          | Some free -> free
          | None -> assert false in
        ignore (Llvm.build_call free [| addr |] "free" builder);
        Mixedvector.null
      | Ssa.Cfree _, _, _ -> failwith "internal: wrong argument to free"
      | Ssa.Cload a, [], [addr] ->
        let a_struct = packing_type a in
        let mem_ptr = Llvm.build_bitcast addr
            (Llvm.pointer_type a_struct) "memptr" builder in
        let lstruct = Llvm.build_load mem_ptr "lstruct" builder in
        unpack_encoded_value lstruct a
      | Ssa.Cload _, _, _ -> failwith "internal: wrong argument to load"
      | Ssa.Cstore a, _, (addr :: _)  ->
        let a_struct = packing_type a in
        let mem_ptr = Llvm.build_bitcast addr
            (Llvm.pointer_type a_struct) "memptr" builder in
        (* The following depends on the encoding of box and pairs and
         * is probably fragile! *)
        let _, venc = Mixedvector.takedrop argenc
            (Profile.singleton Lltype.Pointer) in
        let v_packed = pack_encoded_value (build_truncate_extend venc a) a in
        ignore (Llvm.build_store v_packed mem_ptr builder);
        Mixedvector.null
      | Ssa.Cstore _, _, _ -> failwith "internal: wrong argument to store"
      | Ssa.Cprint _, _, _
      | Ssa.Cpush _, _, _
      | Ssa.Cpop _, _, _
      | Ssa.Ccall _, _, _
        -> assert false
    end

let rec build_letbindings
    (the_module : Llvm.llmodule)
    (func : Llvm.llvalue)
    (ctx: (Ident.t * encoded_value) list)
    (l: Ssa.let_bindings)
  : (Ident.t * encoded_value) list =
  match l with
  | [] -> ctx
  | Ssa.Let((x, a), t) :: lets ->
    let ctx1 = build_letbindings the_module func ctx lets in
    let tenc = build_term the_module func ctx1 t in
    assert_type tenc a;
    (x, tenc) :: ctx1

let build_body
    (the_module : Llvm.llmodule)
    (func : Llvm.llvalue)
    (ctx: (Ident.t * encoded_value) list)
    (l: Ssa.let_bindings)
    (v: Ssa.value)
  : encoded_value =
  let ctx1 = build_letbindings the_module func ctx l in
  build_value the_module ctx1 v

let build_ssa_blocks
    (the_module : Llvm.llmodule)
    (func : Llvm.llvalue)
    (ssa_func : Ssa.t) : unit =
  let label_types = Ident.Table.create () in
  let predecessors = Ident.Table.create () in
  List.iter ssa_func.Ssa.blocks
    ~f:(fun b ->
        let l = Ssa.label_of_block b in
        Ident.Table.set label_types ~key:l.Ssa.name ~data:l.Ssa.message_type;
        List.iter (Ssa.targets_of_block b)
          ~f:(fun p -> Ident.Table.change predecessors p.Ssa.name
                 (function None -> Some 1
                         | Some i -> Some (i+1)))
      );

  let blocks = Ident.Table.create () in
  let phi_nodes = Ident.Table.create () in
  let get_block name =
    match Ident.Table.find blocks name with
    | Some block -> block
    | None ->
      let label = "L" ^ (Ident.to_string name) in
      let block = Llvm.append_block context label func in
      Ident.Table.set blocks ~key:name ~data:block;
      block in
  let connect_to src_block encoded_value dst =
    try
      assert_type encoded_value (Ident.Table.find_exn label_types dst);
      let phi = Ident.Table.find_exn phi_nodes dst in
      (* add (encoded_value, source) to phi node *)
      Mixedvector.add_incoming (encoded_value, src_block) phi
    with Not_found ->
      begin
        (* Insert phi node if block has more than one predecessor. *)
        if Ident.Table.find predecessors dst = Some 1 then
          Ident.Table.set phi_nodes ~key:dst ~data:encoded_value
        else
          begin
            position_at_start (get_block dst) builder;
            let phi = Mixedvector.build_phi
                (encoded_value, src_block) builder in
            Ident.Table.set phi_nodes ~key:dst ~data:phi
          end
      end
  in
  (* make entry block *)
  let entry_block = Llvm.append_block context "entry" func in
  let packed_arg = Llvm.param func 0 in
  Llvm.set_value_name "packed_arg" packed_arg;
  Llvm.position_at_end entry_block builder;
  let arg = unpack_encoded_value packed_arg
      ssa_func.Ssa.entry_label.Ssa.message_type in
  ignore (Llvm.build_br (get_block ssa_func.Ssa.entry_label.Ssa.name) builder);
  connect_to entry_block arg ssa_func.Ssa.entry_label.Ssa.name;
  (* build unconnected blocks *)
  let open Ssa in
  List.iter ssa_func.blocks
    ~f:(fun block ->
        flush stdout;
        match block with
        | Unreachable(src) ->
          Llvm.position_at_end (get_block src.name) builder;
          ignore (Llvm.build_unreachable builder)
        | Direct(src, x, lets, body, dst) ->
          Llvm.position_at_end (get_block src.name) builder;
          let senc = Ident.Table.find_exn phi_nodes src.name in
          assert_type senc src.message_type;
          let ev = build_body the_module func [(x, senc)] lets body in
          let src_block = Llvm.insertion_block builder in
          ignore (Llvm.build_br (get_block dst.name) builder);
          connect_to src_block ev dst.name
        | Branch(src, x, lets, (id, params, body, cases)) ->
          begin
            Llvm.position_at_end (get_block src.name) builder;
            let xenc = Ident.Table.find_exn phi_nodes src.name in
            assert_type xenc src.message_type;
            let ctx = build_letbindings the_module func [(x, xenc)] lets in
            let ebody = build_value the_module ctx body in
            let n = List.length cases in
            assert (n > 0);
            match cases with
            | [(y, v, dst)] ->
              let venc =
                build_value the_module ((y, ebody)::ctx) v in
              let this_block = Llvm.insertion_block builder in
              ignore (Llvm.build_br (get_block dst.name) builder);
              connect_to this_block venc dst.name
            | _ ->
              let cond, yenc =
                let ienc, ya = Mixedvector.takedrop ebody
                    (Profile.singleton (Lltype.Integer (log n))) in
                let cond = Mixedvector.llvalue_of_singleton ienc in
                cond, ya in
              let case_types = Basetype.Data.constructor_types id params in
              let jump_targets =
                List.map2_exn cases case_types
                  ~f:(fun (y, v, dst) a ->
                      (y, build_truncate_extend yenc a), v, dst) in
              let func = Llvm.block_parent (Llvm.insertion_block builder) in
              let case_blocks =
                List.init n
                  ~f:(fun i -> Llvm.append_block context
                         ("case" ^ (string_of_int i)) func) in
              let default_block = List.hd_exn case_blocks in
              let switch =
                Llvm.build_switch cond default_block (n-1) builder in
              (* build case blocks *)
              List.iteri (List.zip_exn case_blocks jump_targets)
                ~f:(fun i (block, ((y, yenc), v, dst)) ->
                    if i > 0 then
                      Llvm.add_case switch
                        (Llvm.const_int (Llvm.integer_type context (log n)) i)
                        block;
                    Llvm.position_at_end block builder;
                    let venc = build_value the_module ((y, yenc)::ctx) v in
                    let this_block = Llvm.insertion_block builder in
                    ignore (Llvm.build_br (get_block dst.name) builder);
                    connect_to this_block venc dst.name
                  )
          end
        | Return(src, x, lets, body, return_type) ->
          Llvm.position_at_end (get_block src.name) builder;
          let xenc = Ident.Table.find_exn phi_nodes src.name in
          let ev = build_body the_module func [(x, xenc)] lets body in
          let pev = pack_encoded_value ev return_type in
          ignore (Llvm.build_ret pev builder)
      )

let llvm_compile (ssa_func : Ssa.t) : Llvm.llmodule =
  let the_module = Llvm.create_module context "int" in

  (* General function declarations *)
  let voidtype = Llvm.void_type context in
  let ptrtype = Llvm.pointer_type (Llvm.i8_type context) in
  let size_lltype =  Llvm.i64_type context in
  let size_to_ptrtype =
    Llvm.function_type ptrtype [| size_lltype |] in
  ignore (Llvm.declare_function "salloc" size_to_ptrtype the_module);
  ignore (Llvm.declare_function "spop" size_to_ptrtype the_module);
  ignore (Llvm.declare_function "gc_alloc" size_to_ptrtype the_module);
  let collect_type =
    Llvm.var_arg_function_type voidtype [| Llvm.i64_type context; ptrtype |] in
  ignore (Llvm.declare_function "gc_collect" collect_type the_module);
  let freetype =
    Llvm.function_type ptrtype [| ptrtype |] in
  ignore (Llvm.declare_function "free" freetype the_module);

  (* Main function *)
  let arg_ty = packing_type ssa_func.Ssa.entry_label.Ssa.message_type in
  let ret_ty = packing_type ssa_func.Ssa.return_type in
  let ft = Llvm.function_type ret_ty (Array.create ~len:1 arg_ty) in
  let func =
    Llvm.declare_function ("Int" ^ ssa_func.Ssa.func_name) ft the_module in
  build_ssa_blocks the_module func ssa_func;
  (* make main function *)
  if ssa_func.Ssa.func_name = "main" then
    begin
      let main_ty = Llvm.function_type int_lltype [| |] in
      let main = Llvm.declare_function "main" main_ty the_module in
      let start_block = Llvm.append_block context "start" main in
      let args = [| Llvm.undef arg_ty |] in
      Llvm.position_at_end start_block builder;
      ignore (Llvm.build_call func args "ret" builder);
      ignore (Llvm.build_ret (Llvm.const_int int_lltype 0) builder)
    end;
  (*  Llvm.dump_module the_module; *)
  the_module
