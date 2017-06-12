open Core_kernel.Std

(********************
 * Values
 ********************)
type constructor = int * (Basetype.Data.id * Basetype.t list)

(** SSA values and terms *)
type value =
  | IntConst of int
  | Var of Ident.t
  | Tuple of value list
  | Proj of value * int * Basetype.t list
  | Inj of constructor * value
  | Out of value * constructor
  | Undef of Basetype.t

(********************
 * Statements
 ********************)

(** Primitive operations *)
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

type term =
  | PrimOp of op_const * value

let rec subst_value (rho: Ident.t -> value) (v: value) =
  match v with
  | Var(x) -> rho x
  | Tuple(vs) -> Tuple(List.map ~f:(subst_value rho) vs)
  | Inj(c, v) -> Inj(c, subst_value rho v)
  | Proj(v, i, b) ->
    begin
      match subst_value rho v with
      | Tuple(vs) -> List.nth_exn vs i
      | w -> Proj(w, i, b)
    end
  | Out(v1, (i, a)) ->
    begin
      match subst_value rho v1 with
      | Inj((j, (id, params)), w) ->
        (* TODO: this is used in cbv.intml. Check that it's really ok. *)
        if i=j then w else
          (* undefined *)
          let ai = match List.nth (Basetype.Data.constructor_types id params) i with
            | Some b -> b
            | None -> assert false in
          Undef(ai)
      | w -> Out(w, (i, a))
    end
  | Undef(a) -> Undef(a)
  | IntConst(i) -> IntConst(i)

let subst_term (rho: Ident.t -> value) (t: term) =
  match t with
  | PrimOp(c, v) -> PrimOp(c, subst_value rho v)

(********************
 * Programs
 ********************)

type let_binding =
  | Let of Ident.t * term

type label = {
  name: Ident.t;
  arg_types: Basetype.t list;
  debug_loc: Ast.Location.t
}

type transfer =
  | Unreachable
  | Direct of label * (value list)
  | Branch of value * (Basetype.Data.id * Basetype.t list) * (Ident.t * label * (value list)) list
  | Return of value * Basetype.t

(** Program blocks *)
type block =
  { label : label;
    args : Ident.t list;
    body : let_binding list;
    jump : transfer }

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

let targets_of_transfer (t : transfer) : label list =
  match t with
  | Unreachable -> []
  | Direct(l, _) -> [l]
  | Branch(_, t, cases) -> List.map cases ~f:(fun (_, l, _) -> l)
  | Return(_, _) -> []

let targets_of_block (b : block) : label list =
  targets_of_transfer b.jump

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
      match List.Assoc.find ~equal:(=) gamma x with
      | Some b -> b
      | None -> failwith ("internal ssa.ml: undefined variable " ^ (Ident.to_string x))
    end
  | Tuple(vs) ->
    let bs = List.map ~f:(typeof_value gamma) vs in
    newty (TupleB(bs))
  | Inj((n, (id, params)), v) ->
    let b = typeof_value gamma v in
    let constructor_types = Data.constructor_types id params in
    (match List.nth constructor_types n with
     | Some b' -> equals_exn b b'
     | None -> failwith "internal ssa.ml: wrong constructor type");
    Basetype.(newty (DataB(id, params)))
  | Proj(v, i, bs) ->
    let a1 = typeof_value gamma v in
    equals_exn a1 (newty (TupleB(bs)));
    begin
      match List.nth bs i with
      | None -> failwith "internal ssa.ml: projection out of bounds"
      | Some b -> b
    end
  | Out(v, (n, (id, params))) ->
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
  | PrimOp(Cprint(_), v) ->
    let b = typeof_value gamma v in
    equals_exn b unitB;
    unitB
  | PrimOp(Cintadd, v)
  | PrimOp(Cintsub, v)
  | PrimOp(Cintmul, v)
  | PrimOp(Cintdiv, v)
  | PrimOp(Cintshl, v)
  | PrimOp(Cintshr, v)
  | PrimOp(Cintsar, v)
  | PrimOp(Cintand, v)
  | PrimOp(Cintor, v)
  | PrimOp(Cintxor, v) ->
    let b = typeof_value gamma v in
    equals_exn b (newty (TupleB [intB; intB]));
    intB
  | PrimOp(Cinteq, v)
  | PrimOp(Cintlt, v)
  | PrimOp(Cintslt, v) ->
    let b = typeof_value gamma v in
    equals_exn b (newty (TupleB [intB; intB]));
    boolB
  | PrimOp(Cintprint, v) ->
    let b = typeof_value gamma v in
    equals_exn b intB;
    unitB
  | PrimOp(Cgcalloc(b), v)
  | PrimOp(Calloc(b), v) ->
    let c = typeof_value gamma v in
    equals_exn c unitB;
    (newty (BoxB b))
  | PrimOp(Cfree(b), v) ->
    let c = typeof_value gamma v in
    equals_exn c (newty (BoxB b));
    unitB
  | PrimOp(Cload(b), v) ->
    let c = typeof_value gamma v in
    equals_exn c (newty (BoxB b));
    b
  | PrimOp(Cstore(b), v) ->
    let c = typeof_value gamma v in
    equals_exn c (newty (TupleB [newty (BoxB b); b]));
    unitB
  | PrimOp(Cpush(b), v) ->
    let c = typeof_value gamma v in
    equals_exn c b;
    unitB
  | PrimOp(Cpop(b), v) ->
    let c = typeof_value gamma v in
    equals_exn c unitB;
    b
  | PrimOp(Ccall(_, b1, b2), v) ->
    let c = typeof_value gamma v in
    equals_exn c b1;
    b2

let rec typecheck_let_bindings
      (gamma: Basetype.t Typing.context)
      (l: let_binding list)
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
    if Basetype.equals a1 a2 then ()
    else failwith "ssa.ml, typecheck_block: type mismatch" in
  let check_label_exn l a =
    match Ident.Table.find blocks l.name with
    | Some block ->
      let b = block.label.arg_types in
      List.iter2_exn ~f:equals_exn a b;
      List.iter2_exn ~f:equals_exn a l.arg_types
    | None -> failwith "internal ssa.ml: wrong argument in jump" in
  let gamma0 = List.zip_exn b.args b.label.arg_types in
  let gamma = typecheck_let_bindings gamma0 b.body in
  match b.jump with
  | Unreachable -> ()
  | Direct(d, v) ->
    let a = List.map ~f:(typeof_value gamma) v in
    check_label_exn d a
  | Branch(v, (id, params), cases) ->
    let constructor_types = Basetype.Data.constructor_types id params in
    let bs = List.zip cases constructor_types in
    begin
      match bs with
      | Some bs ->
        let va = typeof_value gamma v in
        equals_exn va (Basetype.newty
                         (Basetype.DataB(id, params)));
        List.iter bs
          ~f:(fun ((x, d, v), a) ->
            let b = List.map ~f:(typeof_value ((x, a) :: gamma)) v in
            check_label_exn d b)
      | None ->
        failwith "internal ssa.ml: wrong number of cases in branch"
    end
  | Return(v, a) ->
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
  | Inj((k, (id, params)), t) ->
    let cname = List.nth_exn (Basetype.Data.constructor_names id) k in
    Out_channel.output_string oc (Ident.to_string cname);
    Out_channel.output_string oc "(";
    fprint_value oc t;
    Out_channel.output_string oc ")"
  | Proj(t, i, _) ->
    fprint_value oc t;
    Printf.fprintf oc ".%i" i
  | Out(t, (i, _)) ->
    Out_channel.output_string oc "select(";
    fprint_value oc t;
    Printf.fprintf oc ").%i" i
  | Undef(a) ->
    Out_channel.output_string oc "undef(";
    Out_channel.output_string oc (Printing.string_of_basetype a);
    Out_channel.output_string oc ")"
  | IntConst(n) ->
    Printf.fprintf oc "%i" n

let fprint_term (oc: Out_channel.t) (t: term) : unit =
  match t with
  | PrimOp(c, v) ->
    Out_channel.output_string oc (string_of_op_const c);
    Out_channel.output_string oc "(";
    fprint_value oc v;
    Out_channel.output_string oc ")"

let fprint_letbndgs (oc: Out_channel.t) (bndgs: let_binding list) : unit =
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
    Printf.sprintf "%s: %s"
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
  Printf.fprintf oc " l%s(%s) =\n"
    (Ident.to_string b.label.name)
    (param_string b.args b.label.arg_types);
  fprint_letbndgs oc b.body;
  match b.jump with
    | Unreachable ->
      Printf.fprintf oc "unreachable\n"
    | Direct(dst, vs) ->
      Printf.fprintf oc "   l%s(" (Ident.to_string dst.name);
      fprint_values oc vs;
      Printf.fprintf oc ")\n"
    | Branch(cond, (id, _), cases) ->
      let constructor_names = Basetype.Data.constructor_names id in
      Printf.fprintf oc "   case ";
      fprint_value oc cond;
      Printf.fprintf oc " of\n";
      List.iter2_exn constructor_names cases
        ~f:(fun cname (l, lg, lb) ->
          Printf.fprintf oc "   | %s(%s) -> l%s(" (Ident.to_string cname)
            (Ident.to_string l) (Ident.to_string lg.name);
          fprint_values oc lb;
          Printf.fprintf oc ")\n")
    | Return(v, _) ->
      Printf.fprintf oc "   return ";
      fprint_value oc v;
      Printf.fprintf oc "\n"

let fprint_func (oc: Out_channel.t) (func: t) : unit =
  let xs = List.map func.entry_label.arg_types ~f:(fun _ -> Ident.fresh "x") in
  Printf.fprintf oc "%s(%s) : %s = l%s(%s)\n\n"
    func.func_name
    (param_string xs func.entry_label.arg_types)
    (Printing.string_of_basetype func.return_type)
    (Ident.to_string func.entry_label.name)
    (String.concat ~sep:", " (List.map xs ~f:Ident.to_string));
  iter_reachable_blocks func ~f:(fun block ->
    fprint_block oc block;
Out_channel.output_string oc "\n")

let rec to_json_type (a : Basetype.t) : Yojson.Basic.json =
  let open Basetype in
  let open Yojson.Basic in
  match case a with
  | Var -> `Assoc ["var_type", `Int (repr_id a)]
  | Sgn(DataB(id, params)) ->
    `Assoc ["data_type", `Assoc ["type_id", `String (Ident.to_string id);
                            "type_params", `List (List.map params ~f:to_json_type)]]
  | Sgn(TupleB(bs)) ->
    `Assoc ["tuple_type", `List (List.map bs ~f:to_json_type)]
  | Sgn(IntB) ->
    `String "int_type"
  | Sgn(BoxB(b)) ->
    `Assoc ["box_type", to_json_type b]

let rec to_json_constructor ((i, (id, params)) : constructor) : Yojson.Basic.json =
  `Assoc ["number", `Int i;
          "type_id", `String (Ident.to_string id);
          "type_params", `List (List.map params ~f:to_json_type) ]

let rec to_json_value (v: value) : Yojson.Basic.json =
  let open Yojson.Basic in
  match v with
  | Var(x) ->
    `Assoc ["Var", `String (Ident.to_string x)]
  | Tuple(vs) ->
    `Assoc ["Tuple", `List (List.map ~f:to_json_value vs)]
  | Inj(c, t) ->
    `Assoc ["Inj", `Assoc ["constructor", to_json_constructor c;
                          "arg", to_json_value t]]
  | Proj(t, i, bs) ->
    `Assoc ["Proj", `Assoc ["arg", to_json_value t;
                            "tuple_type", `List (List.map bs ~f:to_json_type);
                            "index", `Int i ]]
  | Out(t, c) ->
    `Assoc ["Out", `Assoc ["constructor", to_json_constructor c;
                              "arg", to_json_value t]]
  | Undef(a) ->
    `String "Undefined"
  | IntConst(n) ->
    `Assoc ["int", `Int n]

let to_json_term (t: term) : Yojson.Basic.json =
  let open Yojson.Basic in
  match t with
  | PrimOp(c, v) ->
    `Assoc ["primop", `String (string_of_op_const c);
            "arg", to_json_value v]

let to_json_letbndgs (bndgs: let_binding list) : Yojson.Basic.json =
  `List (List.map (List.rev bndgs)
           ~f:(function
               | Let(x, t) ->
                 `Assoc [Ident.to_string x, to_json_term t]
             ))

let param_json (labels: Ident.t list) (types: Basetype.t list) : Yojson.Basic.json =
  List.zip_exn labels types
  |> List.map ~f:(fun (l, t) ->
      `Assoc [Ident.to_string l, to_json_type t])
  |> fun x -> `List x

let to_json_block (b: block) : Yojson.Basic.json =
  let jump =
  match b.jump with
  | Unreachable ->
    `String "Unreachable"
  | Direct(goal, body) ->
    `Assoc ["direct", `String (Ident.to_string goal.name);
            "args", `List (List.map ~f:to_json_value body)]
  | Branch(cond, (id, params), cases) ->
    `Assoc ["match", to_json_value cond;
            "type_id", `String (Ident.to_string id);
            "type_params", `List (List.map params ~f:to_json_type);
            "cases", `List (List.map cases ~f:(fun (l, lg, lb) ->
                `Assoc ["arg", `String (Ident.to_string l);
                        "direct", `String (Ident.to_string lg.name);
                        "args", `List (List.map ~f:to_json_value lb)]))]
  | Return(body, a) ->
    `Assoc ["return", to_json_value body;
            "return_type", to_json_type a] in
  `Assoc ["block", `String (Ident.to_string b.label.name);
          "args", param_json b.args b.label.arg_types;
          "lets", to_json_letbndgs b.body;
          "jump", jump]

let to_json (func: t) : Yojson.Basic.json =
  let xs = List.map func.entry_label.arg_types ~f:(fun _ -> Ident.fresh "x") in
  `Assoc ["name", `String func.func_name;
          "args", param_json xs func.entry_label.arg_types;
          "return_type", to_json_type func.return_type;
          "entry_block", `String (Ident.to_string func.entry_label.name);
          "blocks", `List (List.map ~f:(fun (_, b) -> to_json_block b)
                             (Ident.Table.to_alist func.blocks))]
