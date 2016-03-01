open Core_kernel.Std

let unPairB a =
  match Basetype.case a with
  | Basetype.Sgn (Basetype.PairB(a1, a2)) -> a1, a2
  | _ -> assert false

let unDataB a =
  match Basetype.case a with
  | Basetype.Sgn (Basetype.DataB(id, params)) ->
     id, params
  | _ -> assert false

type value = Ssa.value * Basetype.t

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

let begin_blockn n ?may_append:(may_append = false) (l: Ssa.label) : value list =
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
    let lastn = List.rev (List.take (List.rev values) n) in
    lastn
  | Some _ ->
     assert false

(* append to existing block *)
let begin_block ?may_append:(may_append = true) (l: Ssa.label) : value =
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

let unit : value =
  Ssa.Unit,
  Basetype.newty (Basetype.UnitB)

let intconst (i: int) =
  Ssa.IntConst(i),
  Basetype.newty (Basetype.IntB)

let boolconst (b: bool) =
  let i = if b then 0 else 1 in
  Ssa.In((Basetype.Data.boolid, i, Ssa.Unit), Basetype.boolB),
  Basetype.boolB

let primop (c: Ssa.op_const) (v: value) : value =
  let vv, va = v in
  let prim = Ident.fresh "prim" in
  let vb =
    let open Basetype in
    let equals_exn a b =
      if equals a b then () else
        failwith "internal translate.ml: type mismatch" in
    match c with
    | Ssa.Cprint(_) ->
       newty UnitB
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
       let intty = newty IntB in
       equals_exn va (newty (PairB(intty, intty)));
       intty
    | Ssa.Cinteq
    | Ssa.Cintlt
    | Ssa.Cintslt ->
       let intty = newty IntB in
       let boolty = newty (DataB(Data.boolid, [])) in
       equals_exn va (newty (PairB(intty, intty)));
       boolty
    | Ssa.Cintprint ->
       let intty = newty IntB in
       equals_exn va intty;
       newty UnitB
    | Ssa.Cgcalloc(b)
    | Ssa.Calloc(b) ->
       equals_exn va (newty UnitB);
       newty (BoxB b)
    | Ssa.Cfree(b) ->
       equals_exn va (newty (BoxB b));
       newty UnitB
    | Ssa.Cload(b) ->
       equals_exn va (newty (BoxB b));
       b
    | Ssa.Cstore(b) ->
       equals_exn va (newty (PairB(newty (BoxB b), b)));
       (newty UnitB)
    | Ssa.Cpush(b) ->
       equals_exn va b;
       (newty UnitB)
    | Ssa.Cpop(b) ->
       equals_exn va (newty UnitB);
       b
    | Ssa.Ccall(_, b1, b2) ->
       equals_exn va b1;
       b2 in
  emit (Ssa.Let((prim, vb), Ssa.Const(c, vv)));
  Ssa.Var prim, vb

let fst (v: value) : value =
  let vv, va = v in
  let a1, a2 = unPairB va in
  match vv with
  | Ssa.Pair(v1, v2) -> v1, a1
  | _ -> Ssa.Fst(vv, a1, a2), a1

let snd (v: value) : value =
  let vv, va = v in
  let a1, a2 = unPairB va in
  match vv with
  | Ssa.Pair(v1, v2) -> v2, a2
  | _ -> Ssa.Snd(vv, a1, a2), a2

let unpair (v: value) : value * value =
  let vv, va = v in
  let a1, a2 = unPairB va in
  match vv with
  | Ssa.Pair(v1, v2) -> (v1, a1), (v2, a2)
  | _ -> (Ssa.Fst(vv, a1, a2), a1), (Ssa.Snd(vv, a1, a2), a2)

let pair (v1: value) (v2: value) : value =
  let vv1, va1 = v1 in
  let vv2, va2 = v2 in
  match vv1, vv2 with
  | Ssa.Fst(x, _, _), Ssa.Snd(y, _, _) when x = y ->
    x,
    Basetype.newty (Basetype.PairB(va1, va2))
  | _ ->
    Ssa.Pair(vv1, vv2),
    Basetype.newty (Basetype.PairB(va1, va2))

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
  (*  ignore (primop (Ssa.Cfree(b)) v);*)
  w

let project (v: value) (a: Basetype.t) : value =
  let _, va = v in
  (*
  Printf.printf "project: %s <= %s\n"
                 (Intlib.Printing.string_of_basetype a)
                 (Intlib.Printing.string_of_basetype va);
  *)
  let select id params x =
    let cs = Basetype.Data.constructor_types id params in
    let rec sel cs n =
      match cs with
      | [] -> assert false
      | c1 :: rest ->
         if Basetype.equals a c1 then
           select x n
         else
           sel rest (n + 1) in
    sel cs 0 in
  if Basetype.equals a va then
    v
  else
    match Basetype.case va with
    | Basetype.Sgn (Basetype.BoxB(c)) ->
       begin
         match Basetype.case c with
         | Basetype.Sgn (Basetype.DataB(id, params)) ->
            let x = unbox v in
            select id params x
         | _ -> assert false
       end
    | Basetype.Sgn (Basetype.DataB(id, params)) ->
       select id params v
    | _ ->
      assert false

let embed (v: value) (a: Basetype.t) : value =
  let _, va = v in
  (*
  Printf.printf "embed: %s <= %s\n"
                 (Intlib.Printing.string_of_basetype va)
                 (Intlib.Printing.string_of_basetype a);
  *)
  if Basetype.equals va a then
    v
  else
    match Basetype.case a with
    | Basetype.Sgn (Basetype.BoxB(c)) ->
      begin
        match Basetype.case c with
        | Basetype.Sgn (Basetype.DataB(id, l)) ->
          let cs = Basetype.Data.constructor_types id l in
          let rec inject l n =
            match l with
            | [] -> assert false
            | b1 :: bs ->
               if Basetype.equals va b1 then
                 let inv = inj n v c in
                 let boxinv = box inv in
                 boxinv
              else
                inject bs (n + 1) in
          inject cs 0
        | _ -> assert false
      end
    | Basetype.Sgn (Basetype.DataB(id, l)) ->
      let cs = Basetype.Data.constructor_types id l in
      let rec inject l n =
        match l with
        | [] -> assert false
        | b1 :: bs ->
          if Basetype.equals va b1 then
            let inv = inj n v a in
            inv
          else
            inject bs (n + 1) in
      inject cs 0
    | _ ->
      assert false

let fill_args (args : Ssa.value list) (v : value list) (dst : Ssa.label)
  : Ssa.value list =
  let vv = List.map ~f:(fun (vv, va) -> vv) v in
  let i = List.length dst.Ssa.arg_types - List.length v in
  let gamma = List.take args i in
  gamma @ vv

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
(* TODO: direkte Sprünge gleich an Vorgänger anhängen *)

let end_block_return (v: value) : unit =
  let vv, va = v in
  match !builder_state with
  | None -> assert false
  | Some s ->
    let block = Ssa.Return(s.cur_label, s.cur_arg, s.cur_lets, vv, va) in
    builder_state := None;
    Ident.Table.add_exn blocks ~key:s.cur_label.Ssa.name ~data:block
