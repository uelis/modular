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
  | Cgcalloc of Basetype.t
  | Calloc of Basetype.t
  | Cfree of Basetype.t
  | Cload of Basetype.t
  | Cstore of Basetype.t
  | Cpush of Basetype.t
  | Cpop of Basetype.t
  | Ccall of string * Basetype.t * Basetype.t

type value =
  | Var of Ident.t
  | Tuple of value list
  | In of (Basetype.Data.id * int * value) * Basetype.t
  | Proj of value * int * Basetype.t list
  | Select of value * (Basetype.Data.id * Basetype.t list) * int
  | Undef of Basetype.t
  | IntConst of int

type term =
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
  | Cgcalloc(_) -> "gcalloc"
  | Calloc(_) -> "alloc"
  | Cfree(_) -> "free"
  | Cload(_) -> "load"
  | Cstore(_) -> "store"
  | Cpush a -> "push{" ^ (Printing.string_of_basetype a) ^ "}"
  | Cpop a -> "pop{" ^ (Printing.string_of_basetype a) ^ "}"
  | Ccall(f, a, b) -> "call(" ^ f ^ ": " ^ (Printing.string_of_basetype a) ^
                      " -> " ^ (Printing.string_of_basetype b) ^ ") "

let rec fprint_value (oc: Out_channel.t) (v: value) : unit =
  match v with
  | Var(x) ->
    Printf.fprintf oc "%s" (Ident.to_string x)
  | Tuple(vs) ->
    Out_channel.output_string oc "(";
    List.iter vs
      ~f:(let sep = ref "" in
          fun v ->
            Out_channel.output_string oc !sep;
            fprint_value oc v;
            sep := ", ");
    Out_channel.output_string oc ")"
  | In((id, k, t), _) ->
    let cname = List.nth_exn (Basetype.Data.constructor_names id) k in
    Out_channel.output_string oc (Ident.to_string cname);
    Out_channel.output_string oc "(";
    fprint_value oc t;
    Out_channel.output_string oc ")"
  | Proj(t, i, _) ->
    fprint_value oc t;
    Printf.fprintf oc ".%i" i
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
  | Tuple(vs) -> Tuple(List.map ~f:(subst_value rho) vs)
  | In((id, i, v), a) -> In((id, i, subst_value rho v), a)
  | Proj(v, i, b) ->
    begin
      match subst_value rho v with
      | Tuple(vs) -> List.nth_exn vs i
      | w -> Proj(w, i, b)
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
  | Const(c, v) -> Const(c, subst_value rho v)

(********************
 * Programs
 ********************)

type let_binding =
  | Let of Ident.t * term
type let_bindings = let_binding list

type label = {
  name: Ident.t;
  arg_types: Basetype.t list
}

type block =
    Unreachable of label
  | Direct of label * (Ident.t list) * let_bindings * (value list) * label
  | Branch of label * (Ident.t list) * let_bindings *
              (Basetype.Data.id * Basetype.t list * value *
               (Ident.t * (value list) * label) list)
  | Return of label * (Ident.t list) * let_bindings * value * Basetype.t

(** Invariant: Any block [b] in the list of blocks must
    be reachable from the entry label by blocks appearing
    before [b] in the list of blocks.
*)
type t = {
  func_name : string;
  entry_label : label;
  blocks : block Ident.Table.t;
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
  | Const(c, v) ->
    Out_channel.output_string oc (string_of_op_const c);
    Out_channel.output_string oc "(";
    fprint_value oc v;
    Out_channel.output_string oc ")"

let fprint_letbndgs (oc: Out_channel.t) (bndgs: let_bindings) : unit =
  List.iter (List.rev bndgs)
    ~f:(function
      | Let(x, t) ->
        Printf.fprintf oc "   let %s = " (Ident.to_string x);
        fprint_term oc t;
        Out_channel.output_string oc "\n"
    )

let param_string (labels: Ident.t list) (types: Basetype.t list) : string =
  List.zip_exn labels types
  |> List.map ~f:(fun (l, t) ->
    Printf.sprintf "%s : %s"
      (Ident.to_string l)
      (Printing.string_of_basetype t))
  |> String.concat ~sep:", "

let fprint_block (oc: Out_channel.t) (b: block) : unit =
  let rec fprint_values oc values =
    match values with
    | [] -> ()
    | v :: vs ->
      fprint_value oc v;
      if vs <> [] then Printf.fprintf oc ", ";
      fprint_values oc vs in
  match b with
    | Unreachable(l) ->
      Printf.fprintf oc " l%s(...) = unreachable\n"
        (Ident.to_string l.name)
    | Direct(l, x, bndgs, body, goal) ->
      Printf.fprintf oc " l%s(%s) =\n"
        (Ident.to_string l.name)
        (param_string x l.arg_types);
      fprint_letbndgs oc bndgs;
      Printf.fprintf oc "   l%s(" (Ident.to_string goal.name);
      fprint_values oc body;
      Printf.fprintf oc ")\n"
    | Branch(la, x, bndgs, (id, _, cond, cases)) ->
      let constructor_names = Basetype.Data.constructor_names id in
      Printf.fprintf oc " l%s(%s) =\n"
        (Ident.to_string la.name)
        (param_string x la.arg_types);
      fprint_letbndgs oc bndgs;
      Printf.fprintf oc "   case ";
      fprint_value oc cond;
      Printf.fprintf oc " of\n";
      List.iter2_exn constructor_names cases
        ~f:(fun cname (l, lb, lg) ->
          Printf.fprintf oc "   | %s(%s) -> l%s(" (Ident.to_string cname)
            (Ident.to_string l) (Ident.to_string lg.name);
          fprint_values oc lb;
          Printf.fprintf oc ")\n")
    | Return(l, x, bndgs, body, _) ->
      Printf.fprintf oc " l%s(%s) =\n"
        (Ident.to_string l.name)
        (param_string x l.arg_types);
      fprint_letbndgs oc bndgs;
      Printf.fprintf oc "   return ";
      fprint_value oc body;
      Printf.fprintf oc "\n"

let fprint_func (oc: Out_channel.t) (func: t) : unit =
  let xs = List.map func.entry_label.arg_types ~f:(fun _ -> Ident.fresh "x") in
  Printf.fprintf oc "%s(%s) : %s = l%s(%s)\n\n"
    func.func_name
    (param_string xs func.entry_label.arg_types)
    (Printing.string_of_basetype func.return_type)
    (Ident.to_string func.entry_label.name)
    (String.concat ~sep:", " (List.map xs ~f:Ident.to_string));
  Ident.Table.iteri func.blocks
    ~f:(fun ~key:l ~data:block ->
      fprint_block oc block;
      Out_channel.output_string oc "\n")

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
  | Tuple(vs) ->
    let bs = List.map ~f:(typeof_value gamma) vs in
    newty (TupleB(bs))
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
  | Proj(v, i, bs) ->
    let a1 = typeof_value gamma v in
    equals_exn a1 (newty (TupleB(bs)));
    begin
      match List.nth bs i with
      | None -> failwith "internal ssa.ml: projection out of bounds"
      | Some b -> b
    end
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
    intB

let typeof_term
      (gamma: Basetype.t Typing.context)
      (t: term)
  : Basetype.t =
  let open Basetype in
  let equals_exn a b =
    if equals a b then () else failwith "internal ssa.ml: type mismatch" in
  match t with
  | Const(Cprint(_), v) ->
    let b = typeof_value gamma v in
    equals_exn b unitB;
    unitB
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
    equals_exn b (newty (TupleB [intB; intB]));
    intB
  | Const(Cinteq, v)
  | Const(Cintlt, v)
  | Const(Cintslt, v) ->
    let b = typeof_value gamma v in
    equals_exn b (newty (TupleB [intB; intB]));
    boolB
  | Const(Cintprint, v) ->
    let b = typeof_value gamma v in
    equals_exn b intB;
    unitB
  | Const(Cgcalloc(b), v)
  | Const(Calloc(b), v) ->
    let c = typeof_value gamma v in
    equals_exn c unitB;
    (newty (BoxB b))
  | Const(Cfree(b), v) ->
    let c = typeof_value gamma v in
    equals_exn c (newty (BoxB b));
    unitB
  | Const(Cload(b), v) ->
    let c = typeof_value gamma v in
    equals_exn c (newty (BoxB b));
    b
  | Const(Cstore(b), v) ->
    let c = typeof_value gamma v in
    equals_exn c (newty (TupleB [newty (BoxB b); b]));
    unitB
  | Const(Cpush(b), v) ->
    let c = typeof_value gamma v in
    equals_exn c b;
    unitB
  | Const(Cpop(b), v) ->
    let c = typeof_value gamma v in
    equals_exn c unitB;
    b
  | Const(Ccall(_, b1, b2), v) ->
    let c = typeof_value gamma v in
    equals_exn c b1;
    b2

let rec typecheck_let_bindings
      (gamma: Basetype.t Typing.context)
      (l: let_bindings)
  : Basetype.t Typing.context =
  match l with
  | [] ->
    gamma
  | Let(v, t) :: ls ->
    let gamma1 = typecheck_let_bindings gamma ls in
    let a = typeof_term gamma1 t in
    (v, a) :: gamma1

let typecheck_block (blocks: block Ident.Table.t) (b: block) : unit =
  let equals_exn a1 a2 =
    if Basetype.equals a1 a2 then () else
      begin
        fprint_block stderr b;
        Printf.fprintf stderr "   %s\n!= %s\n"
          (Printing.string_of_basetype a1)
          (Printing.string_of_basetype a2);
        failwith "ssa.ml, typecheck_block: type mismatch"
      end in
  let check_label_exn l a =
    match Ident.Table.find blocks l.name with
    | Some block ->
      let b = (label_of_block block).arg_types in
      List.iter2_exn ~f:equals_exn a b;
      List.iter2_exn ~f:equals_exn a l.arg_types
    | None -> failwith "internal ssa.ml: wrong argument in jump" in
  match b with
  | Unreachable(_) -> ()
  | Direct(s, x, l, v, d) ->
    let gamma0 = List.zip_exn x s.arg_types in
    let gamma = typecheck_let_bindings gamma0 l in
    let a = List.map ~f:(typeof_value gamma) v in
    check_label_exn d a
  | Branch(s, x, l, (id, params, v, ds)) ->
    let constructor_types = Basetype.Data.constructor_types id params in
    let bs = List.zip ds constructor_types in
    begin
      match bs with
      | Some bs ->
        let gamma0 = List.zip_exn x s.arg_types in
        let gamma = typecheck_let_bindings gamma0 l in
        let va = typeof_value gamma v in
        equals_exn va (Basetype.newty
                         (Basetype.DataB(id, params)));
        List.iter bs
          ~f:(fun ((x, v, d), a) ->
            let b = List.map ~f:(typeof_value ((x, a) :: gamma)) v in
            check_label_exn d b)
      | None ->
        failwith "internal ssa.ml: wrong number of cases in branch"
    end
  | Return(s, x, l, v, a) ->
    let gamma0 = List.zip_exn x s.arg_types in
    let gamma = typecheck_let_bindings gamma0 l in
    let b = typeof_value gamma v in
    equals_exn a b

let typecheck (blocks: block Ident.Table.t) : unit =
  Ident.Table.iteri blocks ~f:(fun ~key:l ~data:b -> typecheck_block blocks b)

let iter_reachable_blocks ~f:(f: block -> unit) (s: t) : unit =
  let visited = Ident.Table.create () in
  let rec sort_blocks i =
    if not (Ident.Table.mem visited i) then
      begin
        Ident.Table.set visited ~key:i ~data:();

        let b = Ident.Table.find_exn s.blocks i in
        f b;
        List.iter (targets_of_block b) ~f:(fun l -> sort_blocks l.name)
      end in
  sort_blocks s.entry_label.name

let make ~func_name:(func_name: string)
      ~entry_label:(entry_label: label)
      ~blocks:(blocks: block Ident.Table.t)
      ~return_type:(return_type: Basetype.t) =
  assert (Ident.Table.find blocks entry_label.name <> None);
  assert (typecheck blocks = ()); (* execute for effect *)
  { func_name = func_name;
    entry_label = entry_label;
    blocks = blocks;
    return_type = return_type }
