open Core_kernel.Std

(********************
 * Values
 ********************)
type value_const =
  | Cundef of Basetype.t
  | Cintconst of int

type op_const =
  | Cprint of string
  | Cintadd
  | Cintsub
  | Cintmul
  | Cintdiv
  | Cinteq
  | Cintlt
  | Cintslt
  | Cintshl
  | Cintshr
  | Cintsar
  | Cintand
  | Cintor
  | Cintxor
  | Cintprint
  | Calloc of Basetype.t
  | Cfree of Basetype.t
  | Cload of Basetype.t
  | Cstore of Basetype.t
  | Cpush of Basetype.t
  | Cpop of Basetype.t
  | Carrayalloc of Basetype.t
  | Carrayfree of Basetype.t
  | Carrayget of Basetype.t
  | Ccall of string * Basetype.t * Basetype.t
  | Cencode of Basetype.t
  | Cdecode of Basetype.t

type value =
  | Var of Ident.t
  | Unit
  | Pair of value * value
  | In of (Basetype.Data.id * int * value) * Basetype.t
  | Fst of value * Basetype.t * Basetype.t
  | Snd of value * Basetype.t * Basetype.t
  | Select of value * (Basetype.Data.id * Basetype.t list) * int
  | Undef of Basetype.t
  | IntConst of int
type term =
  | Val of value
  | Const of op_const * value
             
let string_of_op_const (c: op_const) : string =
  let open Ast in
  match c with
  | Cprint s -> "print(\"" ^ (String.escaped s) ^ "\")"
  | Cintadd -> "intadd"
  | Cintsub -> "intsub"
  | Cintmul -> "intmul"
  | Cintdiv -> "intdiv"
  | Cinteq -> "inteq"
  | Cintlt -> "intlt"
  | Cintslt -> "intslt"
  | Cintshl -> "intshl"
  | Cintshr -> "intshr"
  | Cintsar -> "intsar"
  | Cintand -> "intand"
  | Cintor  -> "intor"
  | Cintxor -> "intxor"
  | Cintprint -> "print"
  | Calloc(_) -> "alloc"
  | Cfree(_) -> "free"
  | Cload(_) -> "load"
  | Cstore(_) -> "store"
  | Carrayalloc _ -> "arrayalloc"
  | Carrayget _ -> "arrayget"
  | Carrayfree _ -> "arrayfree"
  | Cpush a -> "push{" ^ (Printing.string_of_basetype a) ^ "}"
  | Cpop a -> "pop{" ^ (Printing.string_of_basetype a) ^ "}"
  | Ccall(f, a, b) -> "call(" ^ f ^ ": " ^ (Printing.string_of_basetype a) ^
                      " -> " ^ (Printing.string_of_basetype b) ^ ") "
  | Cencode a -> "encode{" ^ (Printing.string_of_basetype a) ^ "}"
  | Cdecode a -> "decode{" ^ (Printing.string_of_basetype a) ^ "}"

let rec fprint_value (oc: Out_channel.t) (v: value) : unit =
  match v with
  | Var(x) ->
    Printf.fprintf oc "%s" (Ident.to_string x)
  | Unit ->
    Printf.fprintf oc "()"
  | Pair(v1, v2) ->
    Out_channel.output_string oc "(";
    fprint_value oc v1;
    Out_channel.output_string oc ", ";
    fprint_value oc v2;
    Out_channel.output_string oc ")"
  | In((id, k, t), _) ->
    let cname = List.nth_exn (Basetype.Data.constructor_names id) k in
    Out_channel.output_string oc cname;
    Out_channel.output_string oc "(";
    fprint_value oc t;
    Out_channel.output_string oc ")"
  | Fst(t, _, _) ->
    fprint_value oc t;
    Out_channel.output_string oc ".1"
  | Snd(t, _, _) ->
    fprint_value oc t;
    Out_channel.output_string oc ".2"
  | Select(t, _, i) ->
    Out_channel.output_string oc "select(";
    fprint_value oc t;
    Printf.fprintf oc ").%i" i
  | Undef(a) ->
    Out_channel.output_string oc "undef(";
    Out_channel.output_string oc (Printing.string_of_basetype a);
    Out_channel.output_string oc ")"
  | IntConst(n) ->
    Printf.fprintf oc "%i" n

let rec subst_value (rho: Ident.t -> value) (v: value) =
  match v with
  | Var(x) -> rho x
  | Unit -> v
  | Pair(v1, v2) -> Pair(subst_value rho v1, subst_value rho v2)
  | In((id, i, v), a) -> In((id, i, subst_value rho v), a)
  | Fst(v, a, b) ->
    begin
      match subst_value rho v with
      | Pair(v1, _) -> v1
      | w -> Fst(w, a, b)
    end
  | Snd(v, a, b) ->
    begin
      match subst_value rho v with
      | Pair(_, v2) -> v2
      | w -> Snd(w, a, b)
    end
  | Select(v1, a, i) ->
    begin
      match subst_value rho v1 with
      | In((_, j, w), a) ->
        (* TODO: this is used in cbv.intml. Check that it's really ok. *)
        if i=j then w else
          (* undefined *)
          let ai =
            match Basetype.case a with
            | Basetype.Sgn (Basetype.DataB(id, params)) ->
              begin
                match List.nth (Basetype.Data.constructor_types id params) i with
                | Some b -> b
                | None -> assert false
              end
            | _ -> assert false in
          Undef(ai)
      | w -> Select(w, a, i)
    end
  | Undef(a) -> Undef(a)
  | IntConst(i) -> IntConst(i)

let subst_term (rho: Ident.t -> value) (t: term) =
  match t with
  | Val(v) -> Val(subst_value rho v)
  | Const(c, v) -> Const(c, subst_value rho v)

(********************
 * Programs
 ********************)

type let_binding =
  | Let of (Ident.t * Basetype.t) * term
type let_bindings = let_binding list

type label = {
  name: Ident.t;
  message_type: Basetype.t
}

type block =
    Unreachable of label
  | Direct of label * Ident.t * let_bindings * value * label
  | Branch of label * Ident.t * let_bindings *
              (Basetype.Data.id * Basetype.t list * value *
               (Ident.t * value * label) list)
  | Return of label * Ident.t * let_bindings * value * Basetype.t

(** Invariant: Any block [b] in the list of blocks must
    be reachable from the entry label by blocks appearing
    before [b] in the list of blocks.
*)
type t = {
  func_name : string;
  entry_label : label;
  blocks : block list;
  return_type: Basetype.t;
}

let label_of_block (b : block) : label =
  match b with
  | Unreachable(l)
  | Direct(l, _, _, _, _)
  | Branch(l, _ , _, _)
  | Return(l, _, _, _, _) -> l

let targets_of_block (b : block) : label list =
  match b with
  | Unreachable(_) -> []
  | Direct(_, _, _, _, l) -> [l]
  | Branch(_, _ , _, (_, _, _, cases)) -> List.map cases ~f:(fun (_, _, l) -> l)
  | Return(_, _, _, _, _) -> []

let fprint_term (oc: Out_channel.t) (t: term) : unit =
  match t with
  | Val(v) ->
    Out_channel.output_string oc "Val(";
    fprint_value oc v;
    Out_channel.output_string oc ")"
  | Const(c, v) ->
    Out_channel.output_string oc (string_of_op_const c);
    Out_channel.output_string oc "(";
    fprint_value oc v;
    Out_channel.output_string oc ")"

let fprint_letbndgs (oc: Out_channel.t) (bndgs: let_bindings) : unit =
  List.iter (List.rev bndgs)
    ~f:(function
      | Let((x, _), t) ->
        Printf.fprintf oc "   let %s = " (Ident.to_string x);
        fprint_term oc t;
        Out_channel.output_string oc "\n"
    )

let fprint_block (oc: Out_channel.t) (b: block) : unit =
  match b with
    | Unreachable(l) ->
      Printf.fprintf oc " l%s(x : %s) = unreachable"
        (Ident.to_string l.name)
        (Printing.string_of_basetype l.message_type)
    | Direct(l, x, bndgs, body, goal) ->
      Printf.fprintf oc " l%s(%s : %s) =\n"
        (Ident.to_string l.name)
        (Ident.to_string x)
        (Printing.string_of_basetype l.message_type);
      fprint_letbndgs oc bndgs;
      Printf.fprintf oc "   l%s(" (Ident.to_string goal.name);
      fprint_value oc body;
      Printf.fprintf oc ")\n"
    | Branch(la, x, bndgs, (id, _, cond, cases)) ->
      let constructor_names = Basetype.Data.constructor_names id in
      Printf.fprintf oc " l%s(%s : %s) =\n"
        (Ident.to_string la.name)
        (Ident.to_string x)
        (Printing.string_of_basetype la.message_type);
      fprint_letbndgs oc bndgs;
      Printf.fprintf oc "   case ";
      fprint_value oc cond;
      Printf.fprintf oc " of\n";
      List.iter2_exn constructor_names cases
        ~f:(fun cname (l, lb, lg) ->
          Printf.fprintf oc "   | %s(%s) -> l%s(" cname
            (Ident.to_string l) (Ident.to_string lg.name);
          fprint_value oc lb;
          Printf.fprintf oc ")\n")
    | Return(l, x, bndgs, body, _) ->
      Printf.fprintf oc " l%s(%s : %s) =\n"
        (Ident.to_string l.name) (Ident.to_string x)
        (Printing.string_of_basetype l.message_type);
      fprint_letbndgs oc bndgs;
      Printf.fprintf oc "   return ";
      fprint_value oc body;
      Printf.fprintf oc "\n"

let fprint_func (oc: Out_channel.t) (func: t) : unit =
  Printf.fprintf oc "%s(x: %s) : %s = l%s(x)\n\n"
    func.func_name
    (Printing.string_of_basetype func.entry_label.message_type)
    (Printing.string_of_basetype func.return_type)
    (Ident.to_string func.entry_label.name);
  List.iter func.blocks
    ~f:(fun block ->
      fprint_block oc block;
      Out_channel.output_string oc "\n")

(* The following functions verify the representation invariants and the
   types in ssa programs. *)

let check_blocks_invariant entry_label blocks =
  let defined_labels = Ident.Table.create () in
  let invoked_labels = Ident.Table.create () in
  Ident.Table.replace invoked_labels ~key:entry_label.name ~data:();
  let check block =
    let l = label_of_block block in
    let ts = targets_of_block block in
    if Ident.Table.mem defined_labels l.name then
      failwith ("ssa invariant: duplicate label definition");
    Ident.Table.replace defined_labels ~key:l.name ~data:();
    if not (Ident.Table.mem invoked_labels l.name) then
      failwith ("ssa invariant: no forward path from entry label");
    List.iter ts ~f:(fun l -> Ident.Table.replace invoked_labels
                                ~key:l.name ~data:()) in
  List.iter blocks ~f:check

let rec typeof_value
          (gamma: Basetype.t Typing.context)
          (v: value)
  : Basetype.t =
  let open Basetype in
  let equals_exn a b =
    if equals a b then () else failwith "internal ssa.ml: type error" in
  match v with
  | Var(x) ->
    begin
      match List.Assoc.find gamma x with
      | Some b -> b
      | None -> failwith ("internal ssa.ml: undefined variable " ^ (Ident.to_string x))
    end
  | Unit ->
    newty UnitB
  | Pair(v1, v2) ->
    let a1 = typeof_value gamma v1 in
    let a2 = typeof_value gamma v2 in
    newty (PairB(a1, a2))
  | In((id, n, v), a) ->
    let b = typeof_value gamma v in
    begin
      match case a with
      | Sgn (DataB(id', params)) ->
        let constructor_types = Data.constructor_types id' params in
        if (id <> id') then failwith "internal ssa.ml: wrong data type";
        (match List.nth constructor_types n with
         | Some b' -> equals_exn b b'
         | None -> failwith "internal ssa.ml: wrong constructor type")
      | _ ->
        fprint_value stderr v;
        failwith "internal ssa.ml: data type expected"
    end;
    a
  | Fst(v, b1, b2) ->
    let a1 = typeof_value gamma v in
    equals_exn a1 (newty (PairB(b1, b2)));
    b1
  | Snd(v, b1, b2) ->
    let a2 = typeof_value gamma v in
    equals_exn a2 (newty (PairB(b1, b2)));
    b2
  | Select(v, (id, params), n) ->
    let a1 = typeof_value gamma v in
    let a = newty (DataB(id, params)) in
    equals_exn a a1;
    let constructor_types = Data.constructor_types id params in
    begin
      match List.nth constructor_types n with
      | Some b -> b
      | None ->
        failwith "internal ssa.ml: unknown constructor"
    end
  | Undef(a) ->
    a
  | IntConst(_) ->
    newty IntB

let typecheck_term
      (gamma: Basetype.t Typing.context)
      (t: term)
      (a: Basetype.t)
  : unit =
  let open Basetype in
  let equals_exn a b =
    if equals a b then () else failwith "internal ssa.ml: type mismatch" in
  match t with
  | Val(v) ->
    let b = typeof_value gamma v in
    equals_exn a b
  | Const(Cprint(_), v) ->
    let b = typeof_value gamma v in
    equals_exn b (newty UnitB);
    equals_exn a (newty UnitB)
  | Const(Cintadd, v)
  | Const(Cintsub, v)
  | Const(Cintmul, v)
  | Const(Cintdiv, v)
  | Const(Cintshl, v)
  | Const(Cintshr, v)
  | Const(Cintsar, v)
  | Const(Cintand, v)
  | Const(Cintor, v)
  | Const(Cintxor, v) ->
    let b = typeof_value gamma v in
    let intty = newty IntB in
    equals_exn b (newty (PairB(intty, intty)));
    equals_exn a intty
  | Const(Cinteq, v)
  | Const(Cintlt, v)
  | Const(Cintslt, v) ->
    let b = typeof_value gamma v in
    let intty = newty IntB in
    let boolty = Basetype.newty (Basetype.DataB(Basetype.Data.boolid, [])) in
    equals_exn b (newty (PairB(intty, intty)));
    equals_exn a boolty
  | Const(Cintprint, v) ->
    let b = typeof_value gamma v in
    let intty = newty IntB in
    equals_exn b intty;
    equals_exn a (newty UnitB)
  | Const(Calloc(b), v) ->
    let c = typeof_value gamma v in
    equals_exn c (newty UnitB);
    equals_exn a (newty (BoxB b))
  | Const(Cfree(b), v) ->
    let c = typeof_value gamma v in
    equals_exn c (newty (BoxB b));
    equals_exn a (newty UnitB)
  | Const(Cload(b), v) ->
    let c = typeof_value gamma v in
    equals_exn c (newty (BoxB b));
    equals_exn a b
  | Const(Cstore(b), v) ->
    let c = typeof_value gamma v in
    equals_exn c (newty (PairB(newty (BoxB b), b)));
    equals_exn a (newty UnitB)
  | Const(Carrayalloc(b), v) ->
    let c = typeof_value gamma v in
    equals_exn c (newty IntB);
    equals_exn a (newty (ArrayB b))
  | Const(Carrayfree(b), v) ->
    let c = typeof_value gamma v in
    equals_exn c (newty (ArrayB b));
    equals_exn a (newty UnitB)
  | Const(Carrayget(b), v) ->
    let c = typeof_value gamma v in
    equals_exn c (newty (PairB(newty (ArrayB b), newty IntB)));
    equals_exn a (newty (BoxB(b)))
  | Const(Cpush(b), v) ->
    let c = typeof_value gamma v in
    equals_exn c b;
    equals_exn a (newty UnitB)
  | Const(Cpop(b), v) ->
    let c = typeof_value gamma v in
    equals_exn c (newty UnitB);
    equals_exn a b
  | Const(Ccall(_, b1, b2), v) ->
    let c = typeof_value gamma v in
    equals_exn c b1;
    equals_exn a b2
  | Const(Cencode b, v) ->
    let c = typeof_value gamma v in
    equals_exn b c
  | Const(Cdecode b, _) ->
    equals_exn b a

let rec typecheck_let_bindings
      (gamma: Basetype.t Typing.context)
      (l: let_bindings)
  : Basetype.t Typing.context =
  match l with
  | [] ->
    gamma
  | Let((v, a), t) :: ls ->
    let gamma1 = typecheck_let_bindings gamma ls in
    typecheck_term gamma1 t a;
    (v, a) :: gamma1

let typecheck_block (label_types: Basetype.t Ident.Table.t) (b: block) : unit =
  let equals_exn a b =
    if Basetype.equals a b then () else failwith "internal ssa.ml: type mismatch" in
  let check_label_exn l a =
    match Ident.Table.find label_types l.name with
    | Some b ->
      equals_exn a b;
      equals_exn l.message_type b
    | None -> failwith "internal ssa.ml: wrong argument in jump" in
  match b with
  | Unreachable(_) -> ()
  | Direct(s, x, l, v, d) ->
    let gamma0 = [(x, s.message_type)] in
    let gamma = typecheck_let_bindings gamma0 l in
    let a = typeof_value gamma v in
    check_label_exn d a
  | Branch(s, x, l, (id, params, v, ds)) ->
    let constructor_types = Basetype.Data.constructor_types id params in
    let bs = List.zip ds constructor_types in
    begin
      match bs with
      | Some bs ->
        let gamma0 = [(x, s.message_type)] in
        let gamma = typecheck_let_bindings gamma0 l in
        let va = typeof_value gamma v in
        equals_exn va (Basetype.newty
                         (Basetype.DataB(id, params)));
        List.iter bs
          ~f:(fun ((x, v, d), a) ->
            let b = typeof_value ((x, a) :: gamma) v in
            check_label_exn d b)
      | None ->
        failwith "internal ssa.ml: wrong number of cases in branch"
    end
  | Return(s, x, l, v, a) ->
    let gamma0 = [(x, s.message_type)] in
    let gamma = typecheck_let_bindings gamma0 l in
    let b = typeof_value gamma v in
    equals_exn a b

let typecheck (blocks: block list) : unit =
  let label_types = Ident.Table.create () in
  List.iter blocks ~f:(fun b ->
    let l = label_of_block b in
    match Ident.Table.add label_types ~key:l.name ~data:l.message_type with
    | `Duplicate -> failwith "internal ssa.ml: duplicte block"
    | `Ok -> ()
  );
  List.iter blocks ~f:(typecheck_block label_types)


let make ~func_name:(func_name: string)
      ~entry_label:(entry_label: label)
      ~blocks:(blocks: block list)
      ~return_type:(return_type: Basetype.t) =
  assert (check_blocks_invariant entry_label blocks = ());
  assert (typecheck blocks = ()); (* execute for effect *)
  { func_name = func_name;
    entry_label = entry_label;
    blocks = blocks;
    return_type = return_type }

