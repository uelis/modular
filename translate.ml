open Core.Std
open Cbvterm

module Ident = Intlib.Ident
module Basetype = Intlib.Basetype
module Ssa = Intlib.Ssa               
module Intast = Intlib.Ast
               
type int_interface = {
  entry: Ssa.label;
  exit: Ssa.label
}

type fragment = {
    eval: int_interface;
    access: int_interface;
    blocks: Ssa.block list;
  }
    
let unitB : Basetype.t =
  Basetype.newty (Basetype.UnitB)
                 
let voidB : Basetype.t =
  Basetype.newty (Basetype.DataB(Basetype.Data.sumid 0, []))
                 
let intB : Basetype.t =
  Basetype.newty (Basetype.IntB)
                  
let pair (a1: Basetype.t) (a2: Basetype.t): Basetype.t =
  Basetype.newty (Basetype.PairB(a1, a2))
           
let unPairB a =
  match Basetype.case a with
  | Basetype.Sgn (Basetype.PairB(a1, a2)) -> a1, a2
  | _ -> assert false
                
let unDataB a =
  match Basetype.case a with
  | Basetype.Sgn (Basetype.DataB(id, params)) ->
     id, params
  | _ -> assert false

(** Simple SSA builder interface *)

let fresh_ssa_name =
  let next_name = ref 0 in
  fun () ->
  let i = !next_name in
  incr next_name;
  i
                
let fresh_label (a : Basetype.t): Ssa.label =
  let i = fresh_ssa_name () in
  { Ssa.name = i;
    Ssa.message_type = a }
    
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
            
let build_unit : value =
  Ssa.Unit, unitB

let build_intconst (i: int) =
  Ssa.IntConst(i), intB
                           
let build_primop (c: Intlib.Ast.op_const) (v: value) : value =
  let vv, va = v in
  let prim = Ident.fresh "prim" in
  let vb =
    let open Basetype in
    let equals_exn a b =
      if equals a b then () else
        failwith "internal translate.ml: type mismatch" in
    match c with
    | Intlib.Ast.Cprint(_) ->
       newty UnitB
    | Intlib.Ast.Cintadd
    | Intlib.Ast.Cintsub
    | Intlib.Ast.Cintmul
    | Intlib.Ast.Cintdiv
    | Intlib.Ast.Cintshl
    | Intlib.Ast.Cintshr
    | Intlib.Ast.Cintsar
    | Intlib.Ast.Cintand
    | Intlib.Ast.Cintor
    | Intlib.Ast.Cintxor ->
       let intty = newty IntB in
       equals_exn va (newty (PairB(intty, intty)));
       intty
    | Intlib.Ast.Cinteq
    | Intlib.Ast.Cintlt
    | Intlib.Ast.Cintslt ->
       let intty = newty IntB in
       let boolty = newty (DataB(Data.boolid, [])) in
       equals_exn va (newty (PairB(intty, intty)));
       boolty
    | Intlib.Ast.Cintprint ->
       let intty = newty IntB in
       equals_exn va intty;
       newty UnitB
    | Intlib.Ast.Calloc(b) ->
       equals_exn va (newty UnitB);
       newty (BoxB b)
    | Intlib.Ast.Cfree(b) ->
       equals_exn va (newty (BoxB b));
       newty UnitB
    | Intlib.Ast.Cload(b) ->
       equals_exn va (newty (BoxB b));
       b
    | Intlib.Ast.Cstore(b) ->
       equals_exn va (newty (PairB(newty (BoxB b), b)));
       (newty UnitB)
    | Intlib.Ast.Carrayalloc(b) ->
       equals_exn va (newty IntB);
       (newty (ArrayB b))
    | Intlib.Ast.Carrayfree(b) ->
       equals_exn va (newty (ArrayB b));
       (newty UnitB)
    | Intlib.Ast.Carrayget(b) ->
       equals_exn va (newty (PairB(newty (ArrayB b), newty IntB)));
       (newty (BoxB(b)))
    | Intlib.Ast.Cpush(b) ->
       equals_exn va b;
       (newty UnitB)
    | Intlib.Ast.Cpop(b) ->
       equals_exn va (newty UnitB);
       b
    | Intlib.Ast.Ccall(_, b1, b2) ->
       equals_exn va b1;
       b2
    | Intlib.Ast.Cencode b ->
       equals_exn b va;
       b
    | Intlib.Ast.Cdecode b ->
       b in
  emit (Ssa.Let((prim, vb), Ssa.Const(c, vv)));
  Ssa.Var prim, vb

let build_fst (v: value) : value =
  let vv, va = v in
  let a1, a2 = unPairB va in
  Ssa.Fst(vv, a1, a2), a1
           
let build_snd (v: value) : value =
  let vv, va = v in
  let a1, a2 = unPairB va in
  Ssa.Snd(vv, a1, a2), a2
           
let build_pair (v1: value) (v2: value) : value =
  let vv1, va1 = v1 in
  let vv2, va2 = v2 in
(*  match vv1, vv2 with
  | Ssa.Fst(x, _, _), Ssa.Snd(y, _, _) when x = y ->
     x, pair va1 va2
  | _ ->*)
     Ssa.Pair(vv1, vv2), pair va1 va2
           
let build_in (i: int) (v: value) (data: Basetype.t) : value =
  let vv, va = v in
  let id, _ = unDataB data in
  Ssa.In((id, i, vv), data), data
                               
let build_select (v: value) (i: int) : value =
  let vv, va = v in
  let id, params = unDataB va in
  let constructor_types = Basetype.Data.constructor_types id params in
  let b =
    match List.nth constructor_types i with
    | Some b -> b
    | None ->
       failwith "internal translate.ml: unknown constructor" in
  Ssa.Select(vv, (id, params), i), b

let build_box (v: value) : value =
  let _, va = v in
  let vbox = build_primop (Intast.Calloc(va)) build_unit in
  ignore (build_primop (Intast.Cstore(va)) v);
  vbox
           
let build_unbox (v: value) : value =
  let _, va = v in
  let b = 
    match Basetype.case va with
    | Basetype.Sgn (Basetype.BoxB(b)) -> b
    | _ -> failwith "build_unbox" in
  let w = build_primop (Intast.Cload(b)) v in
  ignore (build_primop (Intast.Cfree(b)) v);
  w
           
let build_project (v: value) (a: Basetype.t) : value =
  let vv, va = v in
  Printf.printf "project: %s <= %s\n"
                 (Intlib.Printing.string_of_basetype a)
                 (Intlib.Printing.string_of_basetype va);
  let select id params x =
    let cs = Basetype.Data.constructor_types id params in
    let rec sel cs n =
      match cs with
      | [] ->
         failwith "project_sel"
      | c1 :: rest ->
         if Basetype.equals a c1 then
           build_select x n
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
            let x = build_unbox v in
            select id params x 
         | _ -> failwith "project2"
       end
    | Basetype.Sgn (Basetype.DataB(id, params)) ->
       select id params v 
    | _ -> failwith "project3"
                    
let build_embed (v: value) (a: Basetype.t) : value =
  let vv, va = v in
  Printf.printf "embed: %s <= %s\n"
                 (Intlib.Printing.string_of_basetype va)
                 (Intlib.Printing.string_of_basetype a);
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
                 let inv = build_in n v c in
                 let boxinv = build_box inv in
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
            let inv = build_in n v a in
            inv
          else
            inject bs (n + 1) in
      inject cs 0
    | _ ->
      failwith "not_leq"

(* TODO: add assertions to check types *)
let end_block_jump (dst: Ssa.label) (v: value) : Ssa.block =
  let vv, va = v in
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
     let id, params = unDataB va in
     let cs = Basetype.Data.constructor_types id params in
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

(** Functions for working with cbv types *)
           
let rec access_entry_type (a: Cbvtype.t): Basetype.t =
  match Cbvtype.case a with
  | Cbvtype.Var -> failwith "var"
  | Cbvtype.Sgn s ->
     match s with
      | Cbvtype.Nat(m) -> pair m voidB
      | Cbvtype.Fun(m, (x, s, c, y)) ->
        let xc = Cbvtype.code x in
        let yentry = access_entry_type y in
        let xexit = access_exit_type x in
        let sumid = Basetype.Data.sumid 3 in
        let params = [pair s (pair c xc); yentry; xexit] in
        let sum = Basetype.newty (Basetype.DataB(sumid, params)) in
        pair m sum
and access_exit_type (a: Cbvtype.t): Basetype.t =
  match Cbvtype.case a with
  | Cbvtype.Var -> failwith "var"
  | Cbvtype.Sgn s ->
     match s with
     | Cbvtype.Nat(m) -> pair m voidB
     | Cbvtype.Fun(m, (x, s, _, y)) ->
        let yc = Cbvtype.code y in
        let yexit = access_entry_type y in
        let xentry = access_exit_type x in
        let sumid = Basetype.Data.sumid 3 in
        let params = [pair s yc; yexit; xentry] in
        let sum = Basetype.newty (Basetype.DataB(sumid, params)) in
        pair m sum

let ssa_names = Ident.Table.create ()

let ssa_name_of_ident (l: Ident.t) =
  match Ident.Table.find ssa_names l with
  | None ->
     let ientry = fresh_ssa_name () in
     let iexit = fresh_ssa_name () in
     let p = ientry, iexit in
     Ident.Table.add_exn ssa_names l p;
     p
  | Some p -> p
     
let access_of_cbvtype (l: Ident.t) (a: Cbvtype.t) : int_interface =
  let ientry, iexit = ssa_name_of_ident l in
  { entry =
      { Ssa.name = ientry;
        Ssa.message_type = access_entry_type a };
    exit =
      { Ssa.name = iexit;
        Ssa.message_type = access_exit_type a }}
    
let rec code_context (gamma : Cbvtype.t Typing.context) : Basetype.t =
  match gamma with
  | [] -> Basetype.newty Basetype.UnitB
  | (_, a) :: delta ->
     pair (code_context delta) (Cbvtype.code a )
          
let lift_label a l =
  { Ssa.name = l.Ssa.name;
    Ssa.message_type = pair a (l.Ssa.message_type) } 
    
let lift_int_interface a i = {
    entry = lift_label a i.entry;
    exit = lift_label a i.exit
  } 

let lift (a: Basetype.t) (f: fragment) : fragment =
  let lift_block (b: Ssa.block) : Ssa.block =
    match b with
    | Ssa.Direct(l, arg, lets, v, dst) ->
       let l' = lift_label a l in
       let arg' = Ident.variant arg in
       let x = Ident.fresh "x" in
       let lets' =
         lets @
         [Ssa.Let((x, a),
                  Ssa.Val(Ssa.Fst(Ssa.Var(arg'), a, l.Ssa.message_type)));
          Ssa.Let((arg, l.Ssa.message_type),
                  Ssa.Val(Ssa.Snd(Ssa.Var(arg'), a, l.Ssa.message_type)))
         ] in
       let v' = Ssa.Pair(Ssa.Var(x), v) in
       let dst' = lift_label a dst in
       Ssa.Direct(l', arg', lets', v', dst')
    | Ssa.Branch(l, arg, lets, (id, params, v, dsts)) ->
       let l' = lift_label a l in
       let arg' = Ident.variant arg in
       let x = Ident.fresh "x" in
       let lets' =
         lets @
         [Ssa.Let((x, a),
                  Ssa.Val(Ssa.Fst(Ssa.Var(arg'), a, l.Ssa.message_type)));
          Ssa.Let((arg, l.Ssa.message_type),
                  Ssa.Val(Ssa.Snd(Ssa.Var(arg'), a, l.Ssa.message_type)))
         ]  in
       let dsts' = List.map dsts
                           ~f:(fun (y, w, d) ->
                               (y, Ssa.Pair(Ssa.Var(x), w), lift_label a d)) in
       Ssa.Branch(l', arg', lets', (id, params, v, dsts'))
    | Ssa.Return _ -> assert false
    | Ssa.Unreachable _ -> assert false in
  { eval = lift_int_interface a f.eval;
    blocks = List.map ~f: lift_block f.blocks;
    access = lift_int_interface a f.access
  }

let rec build_context_lookup
          (gamma: Cbvtype.t Typing.context)
          (x: Ident.t)
          (v: value)
  : value =
  match gamma with
  | [] -> assert false
  | (y, a) :: delta ->
     if x = y then
       build_snd v
    else
      let v' = build_fst v in
      build_context_lookup delta x v' 

let build_context_map
      (gamma: Cbvtype.t Typing.context)
      (delta: Cbvtype.t Typing.context)
      (code_gamma: value)
    : value =
  let rec values gamma code_gamma =
    match gamma with
    | [] -> []
    | (x, a) :: delta ->
       let code_x = build_snd code_gamma in
       let code_delta = build_fst code_gamma in
       (x, code_x) :: (values delta code_delta) in
  let gamma_values = values gamma code_gamma in
  let delta_values =
    List.map
      ~f:(fun (x, _) -> (x, List.Assoc.find_exn gamma_values x))
      delta in
  let v = List.fold delta_values
                        ~init:build_unit
                        ~f:(fun v (x, vx) -> build_pair v vx) in
  v

let rec translate (t: Cbvterm.t) : fragment =
  match t.t_desc with
  | Var x ->
    let eval = {
      entry = fresh_label (pair t.t_ann (code_context t.t_context));
      exit  = fresh_label (pair t.t_ann (Cbvtype.code t.t_type)) } in
    let access = access_of_cbvtype (Ident.fresh "var") t.t_type in
    let x_access = access_of_cbvtype x t.t_type in
    let block1 =
      let arg = begin_block eval.entry in
      let va = build_fst arg in
      let vgamma = build_snd arg in
      let vx = build_context_lookup t.t_context x vgamma in
      let v = build_pair va vx in
      end_block_jump eval.exit v in
    let block2 =
      let arg = begin_block access.entry in
      end_block_jump x_access.entry arg in
    let block3 =
      let arg = begin_block x_access.exit in
      end_block_jump access.exit arg in
    { eval = eval;
      access = access;
      blocks = [block1; block2; block3]
    }
  | Contr((x, xs), s) ->
     let s_fragment = translate s in
     let xty = List.Assoc.find_exn t.t_context x in
     let xsty = List.map ~f:(fun x' -> List.Assoc.find_exn s.t_context x') xs in
     let summands = List.map ~f:Cbvtype.multiplicity xsty in
     let sumid = Basetype.Data.sumid (List.length summands) in
     let tsum = Basetype.newty (Basetype.DataB(sumid, summands)) in
     let x_access = access_of_cbvtype x xty in
     Printf.printf "X+: %s\n"
                   (Intlib.Printing.string_of_basetype x_access.exit.Ssa.message_type);
     let case_block =
       let _, tx = unPairB x_access.exit.Ssa.message_type in
       let arg = begin_block (fresh_label (pair tsum tx)) in
       let vcopy = build_fst arg in
       let vxexit = build_snd arg in       
       let target y =
         fun c -> let yty = List.Assoc.find_exn s.t_context y in
                  let y_access = access_of_cbvtype y yty in
                  let v = build_pair c vxexit in
                  y_access.exit, v in
       end_block_case vcopy (List.map xs ~f:target) in
     let proj_block =
       let arg = begin_block x_access.exit in
       let vd = build_fst arg in
       let vx = build_snd arg in
       let vsum = build_project vd tsum in
       let v = build_pair vsum vx in
       end_block_jump (Ssa.label_of_block case_block) v in
     let in_blocks =
       List.mapi
         xs
         ~f:(fun i y ->
             let yty = List.Assoc.find_exn s.t_context y in
             let y_access = access_of_cbvtype y yty in
             let arg = begin_block y_access.entry in
             let vc = build_fst arg in
             let vx = build_snd arg in
             let vin_c = build_in i vc tsum in
             let td, _ = unPairB x_access.entry.Ssa.message_type in
             let vd = build_embed vin_c td in
             let v = build_pair vd vx in
             end_block_jump x_access.entry v) in
     { eval = s_fragment.eval;
       access = s_fragment.access;
       blocks = proj_block :: case_block :: in_blocks @ s_fragment.blocks
     }
  | Const(Ast.Cintconst i, []) ->
    let eval = {
      entry = fresh_label (pair t.t_ann unitB);
      exit  = fresh_label (pair t.t_ann intB) } in
    let access = {
      entry = fresh_label (pair (Cbvtype.multiplicity t.t_type) voidB);
      exit  = fresh_label (pair (Cbvtype.multiplicity t.t_type) voidB) } in
    let eval_block =
      let arg = begin_block eval.entry in
      let vstack = build_fst arg in
      let vi = build_intconst i in
      let v = build_pair vstack vi in
      end_block_jump eval.exit v in
    let access_block =
      let arg = begin_block access.entry in
      end_block_jump access.exit arg in
    { eval = eval;
      access = access;
      blocks = [eval_block; access_block]
    }
  | Const(Ast.Cintprint, [s]) ->
     let s_fragment = translate s in
     let eval = {
         entry = fresh_label s_fragment.eval.entry.Ssa.message_type;
         exit  = fresh_label s_fragment.eval.exit.Ssa.message_type } in
     let access = {
         entry = fresh_label s_fragment.access.entry.Ssa.message_type;
         exit  = fresh_label s_fragment.access.exit.Ssa.message_type } in
     let eval_block =
       let arg = begin_block eval.entry in
       end_block_jump s_fragment.eval.entry arg in
     let print_block =
       let arg = begin_block s_fragment.eval.exit in
       let vi = build_snd arg in
       ignore (build_primop (Intast.Cintprint) vi);
       end_block_jump eval.exit arg in
    let access_block1 =
       let arg = begin_block access.entry in
       end_block_jump s_fragment.access.entry arg in
    let access_block2 =
       let arg = begin_block s_fragment.access.exit in
       end_block_jump access.exit arg in
    { eval = eval;
      access = access;
      blocks = [eval_block; print_block; access_block1; access_block2]
               @ s_fragment.blocks
    }
  | Const _ -> failwith "TODO"
  | Fun((x, xty), s) ->
    let s_fragment =
      lift (Cbvtype.multiplicity t.t_type) (translate s) in
    let x_access =
      lift_int_interface
        (Cbvtype.multiplicity t.t_type)
        (access_of_cbvtype x xty) in
    let eval = {
      entry = fresh_label (pair t.t_ann (code_context t.t_context));
      exit  = fresh_label (pair t.t_ann (Cbvtype.code t.t_type)) } in
    let access = access_of_cbvtype (Ident.fresh "fun") t.t_type in
    let eval_block =
      let arg = begin_block eval.entry in
      let vstack = build_fst arg in
      let vgamma = build_snd arg in
      let vclosure = build_embed vgamma (Cbvtype.code t.t_type) in
      let v = build_pair vstack vclosure in
      end_block_jump eval.exit v in
    let block_decode =
      let te = Cbvtype.multiplicity t.t_type in
      let ta = s.t_ann in
      let td = code_context t.t_context in
      let tcx = Cbvtype.code xty in
      let entry = fresh_label (pair te (pair ta (pair td tcx))) in
      let arg = begin_block entry in
      let vadx = build_snd arg in
      let vdx = build_snd vadx in
      let ve = build_fst arg in
      let va = build_fst vadx in
      let vd = build_fst vdx in
      let vx = build_snd vdx in
      let vclosure = build_project vd (code_context t.t_context) in
      (* TODO: Kontexte angleichen *)
      let v = build_pair ve (build_pair va (build_pair vclosure vx)) in
      end_block_jump s_fragment.eval.entry v in
    let case_block =
      let arg = begin_block access.entry in
      let ve = build_fst arg in
      let vreq = build_snd arg in
      end_block_case
        vreq
        [(fun c -> let v = build_pair ve c in
                   Ssa.label_of_block block_decode, v);
         (fun c -> let v = build_pair ve c in
                   s_fragment.access.entry, v);
         (fun c -> let v = build_pair ve c in
                   x_access.exit, v)] in
    let block_in0 =
      let te, tf = unPairB access.exit.Ssa.message_type in
      let arg = begin_block s_fragment.eval.exit in
      let ve = build_fst arg in
      let vv = build_snd arg in
      let vv0 = build_in 0 vv tf in
      let v = build_pair ve vv0 in
      end_block_jump access.exit v in
    let block_in1 =
      let te, tf = unPairB access.exit.Ssa.message_type in      
      let arg = begin_block s_fragment.access.exit in
      let ve = build_fst arg in
      let vy = build_snd arg in
      let vy1 = build_in 1 vy tf in
      let v = build_pair ve vy1 in
      end_block_jump access.exit v in
    let block_in2 =
      let te, tf = unPairB access.exit.Ssa.message_type in      
      let arg = begin_block x_access.entry in
      let ve = build_fst arg in
      let vy = build_snd arg in
      let vx2 = build_in 2 vy tf in
      let v = build_pair ve vx2 in
      end_block_jump access.exit v in
    let convert_var y =
      let te = Cbvtype.multiplicity t.t_type in
      let yty_outer = List.Assoc.find_exn t.t_context y in
      let yty_inner = List.Assoc.find_exn s.t_context y in
      let y_outer_access = access_of_cbvtype y yty_outer in
      let y_inner_access = access_of_cbvtype y yty_inner in
      let tstack_outer, _ = unPairB y_outer_access.entry.Ssa.message_type in
      let tstack_inner, _ = unPairB y_inner_access.entry.Ssa.message_type in
      let entry_block =
        let arg = begin_block y_outer_access.entry in
        let vstack_outer = build_fst arg in
        let vm = build_snd arg in
        let vstack_pair = build_project vstack_outer (pair te tstack_inner) in
        let ve = build_fst vstack_pair in
        let vstack_inner = build_snd vstack_pair in
        let v = build_pair ve (build_pair vstack_inner vm) in
        end_block_jump y_inner_access.entry v in
      let exit_block =
        (* inner program gets lifted! *)
        let lifted_entry = {
            y_inner_access.entry with
            Ssa.message_type = pair te y_inner_access.entry.Ssa.message_type 
          } in
        let arg = begin_block lifted_entry in
        let ve = build_fst arg in
        let vpair = build_snd arg in
        let vstack_inner = build_fst vpair in
        let vm = build_snd vpair in 
        let vstack_outer = build_embed (build_pair ve vstack_inner) tstack_outer in
        let v = build_pair vstack_outer vm in
        end_block_jump y_outer_access.exit v in
      [entry_block; exit_block] in
    let context_blocks =
      t.t_context
      |> List.concat_map ~f:(fun (y, _) -> convert_var y) in
    { eval = eval;
      access = access;
      blocks = [eval_block; block_decode; case_block; block_in0; block_in1; block_in2]
               @ context_blocks
               @ s_fragment.blocks
    }
  (* TODO: embed/project blocks for context *)
  | Fix((f, x, alpha), s) -> failwith "TODO"
  | App(t1, t2) ->
    let t1_fragment = translate t1 in
    let t2_fragment = translate t2 in
    let eval = {
      entry = fresh_label (pair t.t_ann (code_context t.t_context));
      exit  = fresh_label (pair t.t_ann (Cbvtype.code t.t_type)) } in
    let access = access_of_cbvtype (Ident.fresh "app") t.t_type in
    let block1 =
      let arg = begin_block eval.entry in
      let vu = build_fst arg in
      let vgammadelta = build_snd arg in
      let vgamma = build_context_map t.t_context t1.t_context vgammadelta in
      let vdelta = build_context_map t.t_context t2.t_context vgammadelta in
      let embed_val = build_embed (build_pair vu vdelta) t1.t_ann in
      let v = build_pair embed_val vgamma in
      end_block_jump t1_fragment.eval.entry v in
    let block2 =
      let arg = begin_block t1_fragment.eval.exit in
      let ve = build_fst arg in
      let vf = build_snd arg in
      let vu_delta = build_project ve (pair t.t_ann (code_context t2.t_context)) in
      let vu = build_fst vu_delta in
      let vdelta = build_snd vu_delta in
      let vu_f = build_pair vu vf in
      let ve' = build_embed vu_f t2.t_ann in
      let v = build_pair ve' vdelta in
      end_block_jump t2_fragment.eval.entry v in
    let block3 =
      let arg = begin_block t2_fragment.eval.exit in
      let ve = build_fst arg in
      let vx = build_snd arg in
      let vu_f = build_project ve (pair t.t_ann (Cbvtype.code t1.t_type)) in
      let vu = build_fst vu_f in
      let vf = build_snd vu_f in
      let vufx = build_pair vu (build_pair vf vx) in
      let td, tfunacc = unPairB t1_fragment.access.entry.Ssa.message_type in
      let vfunacc = build_in 0 vufx tfunacc in
      let vd = build_embed build_unit td in
      let v = build_pair vd vfunacc in
      end_block_jump t1_fragment.access.entry v in
    let block5 =
      let arg = begin_block access.entry in
      let td, tfunacc = unPairB t1_fragment.access.entry.Ssa.message_type in
      let vd = build_embed build_unit td in      
      let v = build_pair vd (build_in 1 arg tfunacc) in
      end_block_jump t1_fragment.access.entry v in
    let block7 =
      let arg = begin_block t2_fragment.access.exit in
      let td, tfunacc = unPairB t1_fragment.access.entry.Ssa.message_type in
      let vd = build_embed build_unit td in      
      let v = build_pair vd (build_in 2 arg tfunacc) in
      end_block_jump t1_fragment.access.entry v in
    let case_block =
      let arg = begin_block t1_fragment.access.exit in
      let vfun = build_snd arg in
      end_block_case
        vfun
        [ (fun c -> eval.exit, c);
          (fun c -> access.exit, c);
          (fun c -> t2_fragment.access.entry, c) ] in
    { eval = eval;
      access = access;
      blocks = [block1; block2; block3; block5; block7; case_block]
               @ t1_fragment.blocks
               @ t2_fragment.blocks
    }
  | Ifz(tc, t1, t2) -> failwith "TODO"

let print_fragment f =
  List.iter f.blocks ~f:(fun block -> Ssa.fprint_block stdout block);
  Printf.printf "\n\n"

let to_ssa t =
  let f = translate t in
  let ret_ty = f.eval.exit.Ssa.message_type in
  let return_block =
    let arg = begin_block f.eval.exit in
    end_block_return arg in
  let access_exit_block =
    let arg = begin_block f.access.exit in
    end_block_jump f.access.exit arg in
  let blocks = Int.Table.create () in
  List.iter (return_block :: access_exit_block :: f.blocks)
    ~f:(fun b ->
      let i = (Ssa.label_of_block b).Ssa.name in
      Int.Table.replace blocks ~key:i ~data:b
    );
  let visited = Int.Table.create () in
  let rev_sorted_blocks = ref [] in
  let rec sort_blocks i =
    if not (Int.Table.mem visited i) then
      begin
        Printf.printf "%i\n" i;
        Int.Table.replace visited ~key:i ~data:();

        let b = Int.Table.find_exn blocks i in
        Ssa.fprint_block stdout b; 
        rev_sorted_blocks := b :: !rev_sorted_blocks;
        List.iter (Ssa.targets_of_block b)
          ~f:(fun l -> sort_blocks l.Ssa.name)
      end in
  sort_blocks f.eval.entry.Ssa.name;
  Printf.printf "finisx%!\n";
  Ssa.make
    ~func_name:"main"
    ~entry_label:f.eval.entry
    ~blocks: (List.rev !rev_sorted_blocks)
    ~return_type: ret_ty
