open Core_kernel.Std

let unTupleB a =
  match Basetype.case a with
  | Basetype.Sgn (Basetype.TupleB bs) -> bs
  | _ -> assert false

let unDataB a =
  match Basetype.case a with
  | Basetype.Sgn (Basetype.DataB(id, params)) -> id, params
  | _ -> assert false

type value = Ssa.value * Basetype.t

let typeof (v: value) : Basetype.t =
  snd v

type builder_state_type = {
    cur_label: Ssa.label;
    cur_arg: Ident.t list;
    cur_lets: Ssa.let_bindings;
    cur_implicit_args: Ssa.value list
  }

let blocks = Ident.Table.create ()
let builder_state =
  ref (None : builder_state_type option)

let predecessors : (Ssa.block list) Ident.Table.t = Ident.Table.create ()

let reset () : unit =
  Ident.Table.clear blocks;
  Ident.Table.clear predecessors;
  builder_state := None

let emit (l : Ssa.let_binding) : unit =
  match !builder_state with
  | None -> failwith "emit"
  | Some s ->
     builder_state := Some { s with cur_lets = l :: s.cur_lets }

let begin_block ?may_append:(may_append = true) (l: Ssa.label) : value list =
  assert (l.Ssa.arg_types <> []);
  match !builder_state with
  | None ->
    let values =
      match Ident.Table.find predecessors l.Ssa.name with
      | Some [Ssa.Direct(l1, args, lets, vv, l')] when may_append ->
        assert (l.Ssa.name = l'.Ssa.name);
        Ident.Table.remove blocks l1.Ssa.name;
        Ident.Table.remove_multi predecessors l.Ssa.name;
        builder_state := Some { cur_label = l1; cur_arg = args; cur_lets = lets; cur_implicit_args = vv };
        List.zip_exn vv l'.Ssa.arg_types
      | _ ->
        let args = List.map ~f:(fun _ -> Ident.fresh "x") l.Ssa.arg_types in
        let iargs = List.map ~f:(fun x -> Ssa.Var x) args in
        builder_state := Some { cur_label = l; cur_arg = args; cur_lets = []; cur_implicit_args = iargs };
        List.zip_exn iargs l.Ssa.arg_types in
    values
  | Some _ ->
     assert false

let begin_blockn ?may_append:(may_append = true) (n: int) (l: Ssa.label) : value list =
  List.rev (List.take (List.rev (begin_block ~may_append:may_append l)) n)

let begin_block1 ?may_append:(may_append = true) (l: Ssa.label) : value =
  match begin_blockn ~may_append:may_append 1 l with
  | [v] -> v
  | _ -> assert false

let begin_block2 ?may_append:(may_append = true) (l: Ssa.label) : value * value =
  match begin_blockn ~may_append:may_append 2 l with
  | [v1; v2] -> v1, v2
  | _ -> assert false

let begin_block3 ?may_append:(may_append = true) (l: Ssa.label) : value * value * value =
  match begin_blockn ~may_append:may_append 3 l with
  | [v1; v2; v3] -> v1, v2, v3
  | _ -> assert false

let begin_block4 ?may_append:(may_append = true) (l: Ssa.label) : value * value * value * value =
  match begin_blockn ~may_append:may_append 4 l with
  | [v1; v2; v3; v4] -> v1, v2, v3, v4
  | _ -> assert false

let unit : value =
  Ssa.Tuple [],
  Basetype.unitB

let intconst (i: int) =
  Ssa.IntConst(i),
  Basetype.intB

let boolconst (b: bool) =
  let i = if b then 0 else 1 in
  Ssa.In((Basetype.Data.boolid, i, Ssa.Tuple []), Basetype.boolB),
  Basetype.boolB

let primop (c: Ssa.op_const) (v: value) : value =
  let vv, va = v in
  let prim = Ident.fresh "prim" in
  let vb =
    let open Basetype in
    match c with
    | Ssa.Cprint(_) ->
      Basetype.unitB
    | Ssa.Cintadd
    | Ssa.Cintsub
    | Ssa.Cintmul
    | Ssa.Cintdiv
    | Ssa.Cintshl
    | Ssa.Cintshr
    | Ssa.Cintsar
    | Ssa.Cintand
    | Ssa.Cintor
    | Ssa.Cintxor ->
      assert (equals va (pairB intB intB));
      intB
    | Ssa.Cinteq
    | Ssa.Cintlt
    | Ssa.Cintslt ->
      assert (equals va (pairB intB intB));
      Basetype.boolB
    | Ssa.Cintprint ->
      assert (equals va intB);
      unitB
    | Ssa.Cgcalloc(b)
    | Ssa.Calloc(b) ->
      assert (equals va unitB);
      newty (BoxB b)
    | Ssa.Cfree(b) ->
      assert (equals va (newty (BoxB b)));
      unitB
    | Ssa.Cload(b) ->
      assert (equals va (newty (BoxB b)));
      b
    | Ssa.Cstore(b) ->
      assert (equals va (pairB (newty (BoxB b)) b));
      unitB
    | Ssa.Cpush(b) ->
      assert (equals va b);
      unitB
    | Ssa.Cpop(b) ->
      assert (equals va unitB);
      b
    | Ssa.Ccall(_, b1, b2) ->
      assert (equals va b1);
      b2 in
  emit (Ssa.Let(prim, Ssa.Const(c, vv)));
  Ssa.Var prim, vb

let tuple (vs: value list) : value =
  let values, types = List.unzip vs in
  Ssa.Tuple values,
  Basetype.newty (Basetype.TupleB types)

let untuple (v: value) : value list =
  let vv, vb = v in
  let bs = unTupleB vb in
  match vv with
  | Ssa.Tuple vs -> List.zip_exn vs bs
  | _ -> List.mapi bs ~f:(fun i bi -> Ssa.Proj(vv, i, bs), bi)

let pair (v1: value) (v2: value) : value =
  tuple [v1; v2]

let unpair (v: value) : value * value =
  match untuple v with
  | [v1; v2] -> v1, v2
  | _ -> assert false

let proj (v: value) (i: int) : value =
  let vv, va = v in
  let bs = unTupleB va in
  match vv with
  | Ssa.Tuple vs -> List.nth_exn vs i, List.nth_exn bs i
  | _ -> Ssa.Proj(vv, i, bs), List.nth_exn bs i

let inj (i: int) (v: value) (data: Basetype.t) : value =
  let vv, _ = v in
  let id, _ = unDataB data in
  Ssa.In((id, i, vv), data), data

let select (v: value) (i: int) : value =
  let vv, va = v in
  let id, params = unDataB va in
  let constructor_types = Basetype.Data.constructor_types id params in
  let b =
    match List.nth constructor_types i with
    | Some b -> b
    | None ->
       failwith "internal translate.ml: unknown constructor" in
  Ssa.Select(vv, (id, params), i), b

let box (v: value) : value =
  let _, va = v in
  let vbox = primop (Ssa.Cgcalloc(va)) unit in
  ignore (primop (Ssa.Cstore(va)) (pair vbox v));
  vbox

let unbox (v: value) : value =
  let _, va = v in
  let b =
    match Basetype.case va with
    | Basetype.Sgn (Basetype.BoxB(b)) -> b
    | _ -> failwith "unbox" in
  let w = primop (Ssa.Cload(b)) v in
  w

let index_of_ctor id params ctor =
  let cs = Basetype.Data.constructor_types id params in
  match List.findi cs ~f:(fun _ -> Basetype.equals ctor) with
  | Some(i, _) -> i
  | None -> assert false

let project (v: value) (a: Basetype.t) : value =
  let _, typeof_v = v in
  if Basetype.equals typeof_v a then v
  else
    match Basetype.case typeof_v with
    | Basetype.Sgn(Basetype.DataB(id, params)) ->
      let i = index_of_ctor id params a in
      select v i
    | Basetype.Sgn(Basetype.BoxB(c)) ->
      let id, params = unDataB c in
      let i = index_of_ctor id params a in
      let x = unbox v in
      select x i
    | _ -> assert false

let embed (v: value) (a: Basetype.t) : value =
  let _, typeof_v = v in
  if Basetype.equals typeof_v a then v
  else
    match Basetype.case a with
    | Basetype.Sgn(Basetype.DataB(id, params)) ->
      let i = index_of_ctor id params typeof_v in
      inj i v a
    | Basetype.Sgn(Basetype.BoxB(c)) ->
      let id, params = unDataB c in
      let i = index_of_ctor id params typeof_v in
      box (inj i v c)
    | _ -> assert false

let fill_args (args : Ssa.value list) (v : value list) (dst : Ssa.label)
  : Ssa.value list =
  let vv = List.map ~f:(fun (vv, va) -> vv) v in
  let need_args = List.length dst.Ssa.arg_types - List.length v in
  let needed_args = List.take args need_args in
  needed_args @ vv

(* TODO: add assertions to check types *)
let end_block_jump (dst: Ssa.label) (v: value list) : unit =
  match !builder_state with
  | None -> assert false
  | Some s ->
    let argv = fill_args s.cur_implicit_args v dst in
    let block = Ssa.Direct(s.cur_label, s.cur_arg, s.cur_lets, argv, dst) in
    builder_state := None;
    Ident.Table.add_exn blocks ~key:s.cur_label.Ssa.name ~data:block;
    Ident.Table.add_multi predecessors ~key:dst.Ssa.name ~data:block

(* TODO: add assertions to check types *)
let end_block_unreachable () : unit =
  match !builder_state with
  | None -> assert false
  | Some s ->
    let block = Ssa.Unreachable(s.cur_label) in
    builder_state := None;
    Ident.Table.add_exn blocks ~key:s.cur_label.Ssa.name ~data:block

(* TODO: add assertions to check types *)
(* TODO: the functions in [targets] must not create new let-definitions *)
let end_block_case (v: value) (targets: (value -> Ssa.label * (value list)) list) : unit =
  let vv, va = v in
  match !builder_state with
  | None -> assert false
  | Some s ->
     let id, params = unDataB va in
     let cs = Basetype.Data.constructor_types id params in
     let branches =
       List.map (List.zip_exn targets cs)
                ~f:(fun (t, a) ->
                    let x = Ident.fresh "x" in
                    let vx = Ssa.Var x, a in
                    let dst, arg = t vx in
                    let argv = fill_args s.cur_implicit_args arg dst in
                    x, argv, dst
           ) in
     let block = Ssa.Branch(s.cur_label, s.cur_arg, s.cur_lets,
                            (id, params, vv, branches)) in
     builder_state := None;
     Ident.Table.add_exn blocks ~key:s.cur_label.Ssa.name ~data:block;
     List.iter branches
       ~f:(fun (_, _, dst) ->
           Ident.Table.add_multi predecessors ~key:dst.Ssa.name ~data:block)

let end_block_return (v: value) : unit =
  let vv, va = v in
  match !builder_state with
  | None -> assert false
  | Some s ->
    let block = Ssa.Return(s.cur_label, s.cur_arg, s.cur_lets, vv, va) in
    builder_state := None;
    Ident.Table.add_exn blocks ~key:s.cur_label.Ssa.name ~data:block
