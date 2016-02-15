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
    cur_arg: Ident.t;
    cur_lets: Ssa.let_bindings
  }

let builder_state =
  ref (None : builder_state_type option)

let emit (l : Ssa.let_binding) : unit =
  match !builder_state with
  | None -> failwith "emit"
  | Some s ->
     builder_state := Some { s with cur_lets = l :: s.cur_lets }

let begin_block (l: Ssa.label) : value =
  match !builder_state with
  | None ->
     let argid = Ident.fresh "arg" in
     let v = Ssa.Var argid, l.Ssa.message_type in
     builder_state := Some { cur_label = l; cur_arg = argid; cur_lets = [] };
     v
  | Some _ ->
     assert false

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
  Ssa.Fst(vv, a1, a2), a1

let snd (v: value) : value =
  let vv, va = v in
  let a1, a2 = unPairB va in
  Ssa.Snd(vv, a1, a2), a2

let unpair (v: value) : value * value =
  let v1 = fst v in
  let v2 = snd v in
  v1, v2

let pair (v1: value) (v2: value) : value =
  let vv1, va1 = v1 in
  let vv2, va2 = v2 in
(*  match vv1, vv2 with
  | Ssa.Fst(x, _, _), Ssa.Snd(y, _, _) when x = y ->
    x,
    Basetype.newty (Basetype.PairB(va1, va2))
    | _ ->*)
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
      | [] ->
         failwith "project_sel"
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
         | _ -> failwith "project2"
       end
    | Basetype.Sgn (Basetype.DataB(id, params)) ->
       select id params v
    | _ ->
       failwith "project3"

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
            | [] -> failwith "not_leq"
            | b1 :: bs ->
               if Basetype.equals va b1 then
                 let inv = inj n v c in
                 let boxinv = box inv in
                 boxinv
              else
                inject bs (n + 1) in
          inject cs 0
        | _ -> failwith "not_leq"
      end
    | Basetype.Sgn (Basetype.DataB(id, l)) ->
      let cs = Basetype.Data.constructor_types id l in
      let rec inject l n =
        match l with
        | [] -> failwith "not_leq"
        | b1 :: bs ->
          if Basetype.equals va b1 then
            let inv = inj n v a in
            inv
          else
            inject bs (n + 1) in
      inject cs 0
    | _ ->
      failwith "not_leq"

(* TODO: add assertions to check types *)
let end_block_jump (dst: Ssa.label) (v: value) : Ssa.block =
  let vv, _ = v in
  match !builder_state with
  | None -> assert false
  | Some s ->
    builder_state := None;
    Ssa.Direct(s.cur_label, s.cur_arg, s.cur_lets, vv, dst)

(* TODO: add assertions to check types *)
(* TODO: the functions in [targets] must not create new let-definitions *)
let end_block_case (v: value) (targets: (value -> Ssa.label * value) list) : Ssa.block =
  let vv, va = v in
  match !builder_state with
  | None -> assert false
  | Some s ->
   (*  let l = s.cur_label in
     let arg = s.cur_arg in
     let lets = s.cur_lets in *)
     let id, params = unDataB va in
     let cs = Basetype.Data.constructor_types id params in
     (*
     let make_branch (target, a) =
       builder_state := None;
       let x = begin_block a in
       let dst, (v, _) = target vx in
       if !builder_state.cur_lets = [] then
         !builder_state.cur_arg, v, dst
       else

                    let x = Ident.fresh "x" in
                    let vx = Ssa.Var x, a in
                    let dst, (arg, _) = t vx in
                    x, arg, dst
     *)
     let branches =
       List.map (List.zip_exn targets cs)
                ~f:(fun (t, a) ->
                    let x = Ident.fresh "x" in
                    let vx = Ssa.Var x, a in
                    let dst, (arg, _) = t vx in
                    x, arg, dst
                ) in
     builder_state := None;
     Ssa.Branch(s.cur_label, s.cur_arg, s.cur_lets,
                (id, params, vv, branches))

let end_block_return (v: value) : Ssa.block =
  let vv, va = v in
  match !builder_state with
  | None -> assert false
  | Some s ->
    builder_state := None;
    Ssa.Return(s.cur_label, s.cur_arg, s.cur_lets, vv, va)
