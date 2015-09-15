open Core.Std
open Cbvterm

module Ident = Intlib.Ident
module Basetype = Intlib.Basetype
module Ssa = Intlib.Ssa               
               
type int_interface = {
  entry: Ssa.label;
  exit: Ssa.label
}

type fragment = {
    eval: int_interface;
    access: int_interface;
    blocks: Ssa.block list;
  }

let fresh_label : Basetype.t -> Ssa.label =
  let next_label = ref 0 in
  fun a ->
  let i = !next_label in
  incr next_label;
  { Ssa.name = i;
    Ssa.message_type = a }
    
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

(* Simple SSA builder interface *)
    
type value = Ssa.value * Basetype.t

type builder_state_type = {
    cur_label: Ssa.label;
    cur_arg: Ident.t;
    cur_lets: Ssa.let_bindings
  }

let builder_state =
  ref (None : builder_state_type option)

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
  Ssa.Unit, Basetype.newty Basetype.UnitB

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
  Ssa.Pair(vv1, vv2), pair va1 va2
           
let build_in (i: int) (v: value) (data: Basetype.t) : value =
  let vv, va = v in
  let id, _ = unDataB data in
  Ssa.In((id, i, vv), data), data
           
let build_project (v: value) (a: Basetype.t) : value =
  failwith "TODO"
           
let build_embed (v: value) (a: Basetype.t) : value =
  failwith "TODO"

let end_block_jump (dst: Ssa.label) (v: value) : Ssa.block =
  let vv, va = v in
  match !builder_state with
  | None -> assert false
  | Some s ->
     (* TODO: check types *)
     Ssa.Direct(s.cur_label, s.cur_arg, s.cur_lets, vv, dst)
           
let end_block_switch (v: value) (targets: (value -> Ssa.label * value) list) : Ssa.block =
  failwith "TODO"
(*
type interface = {
  access_entry: Ssa.label;
  access_exit: Ssa.label;
  eval_entry: Ssa.label;
  eval_exit: Ssa.label
}
*)

let access_of_cbvtype : Ident.t -> Cbvtype.t -> int_interface =
  failwith "TODO"
    
let value_type_of_cbvtype : Cbvtype.t -> Basetype.t =
  failwith "TODO"

let code_context : Cbvtype.t Typing.context -> Basetype.t =
  failwith "TODO"
    
let embed: Ssa.value -> Basetype.t -> Basetype.t -> Ssa.let_bindings * Ssa.value =
  failwith "TODO"

let project: Ssa.value -> Basetype.t -> Basetype.t -> Ssa.let_bindings * Ssa.value =
  failwith "TODO"

let lift: Basetype.t -> fragment -> fragment =
  failwith "TODO"

let rec context_lookup
          (gamma: Cbvtype.t Typing.context)
          (x: Ident.t)
          (v: Ssa.value)
  : Ssa.value =
  match gamma with
  | [] -> assert false
  | (y, a) :: delta ->
    if x = y then
      Ssa.Snd(v, code_context delta, Cbvtype.code a)
    else
      let v' = Ssa.Fst(v, code_context delta, Cbvtype.code a) in
      context_lookup delta x v' 

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
      entry = fresh_label (code_context t.t_context);
      exit  = fresh_label (Cbvtype.code t.t_type) } in
    let access = access_of_cbvtype (Ident.fresh "var") t.t_type in
    let x_access = access_of_cbvtype x t.t_type in
    let block1 =
      (*
      let arg = begin_block eval.entry in
      let va = build_fst arg in
      let vgamma = build_snd arg in
       *)
      let arg = Ident.fresh "arg" in
      let ta = t.t_ann in
      let tgamma = code_context t.t_context in
      let va = Ssa.Fst(Ssa.Var(arg), ta, tgamma) in
      let vgamma = Ssa.Snd(Ssa.Var(arg), ta, tgamma) in
      let vx = context_lookup t.t_context x vgamma in
      Ssa.Direct(eval.entry, arg, [],
                 Ssa.Pair(va, vx), eval.exit) in
    let block2 =
      let arg = Ident.fresh "arg" in
      Ssa.Direct(access.entry, arg, [],
                 Ssa.Var arg, x_access.entry) in
    let block3 =
      let arg = Ident.fresh "arg" in
      Ssa.Direct(x_access.exit, arg, [],
                 Ssa.Var arg, x_access.exit) in
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
     let case_block =
       let _, tx = unPairB x_access.entry.Ssa.message_type in
       let arg = begin_block (fresh_label (pair tsum tx)) in
       let vcopy = build_fst arg in
       let vxexit = build_snd arg in       
       let target y =
         fun c -> let yty = List.Assoc.find_exn s.t_context y in
                  let y_access = access_of_cbvtype y yty in
                  let v = build_pair c vxexit in
                  y_access.exit, v in
       end_block_switch vcopy (List.map xs ~f:target) in
(*       
       let _, tx = unPairB x_access.entry.Ssa.message_type in
       let l = fresh_label (pair tsum tx) in
       let arg = Ident.fresh "arg" in
       let vcopy = Ssa.Fst(Ssa.Var(arg), tsum, tx) in
       let vxexit = Ssa.Snd(Ssa.Var(arg), tsum, tx) in
       let sumid, summands = unDataB tsum in
       Ssa.Branch(l, arg, [],
                  (sumid, summands,
                   vcopy,
                   List.map xs
                     ~f:(fun x' ->
                         let c = Ident.fresh "c" in
                         let x'ty = List.Assoc.find_exn s.t_context x' in
                         let x'_access = access_of_cbvtype x x'ty in
                         c, Ssa.Pair(Ssa.Var(c), vxexit), x'_access.exit)
                  )) in*)
     let proj_block =
       let arg = begin_block x_access.entry in
       let vd = build_fst arg in
       let vx = build_snd arg in
       let vsum = build_project vd tsum in
       let v = build_pair vsum vx in
       end_block_jump (Ssa.label_of_block case_block) v in
(*         
       let arg = Ident.fresh "arg" in
       let td, tx = unPairB x_access.entry.Ssa.message_type in
       let vd = Ssa.Fst(Ssa.Var(arg), td, tx) in
       let vx = Ssa.Snd(Ssa.Var(arg), td, tx) in
       let proj_lets, vsum = project vd tsum td in
       Ssa.Direct(x_access.entry, arg, proj_lets,
                  Ssa.Pair(vsum, vx), Ssa.label_of_block case_block) in *)
     let in_blocks =
       List.mapi
         xs
         ~f:(fun i y ->
             let yty = List.Assoc.find_exn s.t_context y in
             let y_access = access_of_cbvtype y yty in
             let arg = begin_block y_access.exit in
             let vc = build_fst arg in
             let vx = build_snd arg in
             let vin_c = build_in i vc tsum in
             let td, _ = unPairB x_access.exit.Ssa.message_type in
             let vd = build_embed vin_c td in
             let v = build_pair vd vx in
             end_block_jump x_access.exit v) in
             (*
     let in_blocks =
       List.mapi
         xs
         ~f:(fun i x' ->
             let x'ty = List.Assoc.find_exn s.t_context x' in
             let x'_access = access_of_cbvtype x x'ty in
             let arg = Ident.fresh "arg" in
             let tc, tx = unPairB x'_access.exit.Ssa.message_type in
             let vc = Ssa.Fst(Ssa.Var(arg), tc, tx) in
             let vx = Ssa.Snd(Ssa.Var(arg), tc, tx) in
             let td, _ = unPairB x_access.exit.Ssa.message_type in
             let vin_c = Ssa.In((sumid, i, vc), tsum) in
             let embed_lets, vd = embed vin_c tsum td in
             Ssa.Direct(x'_access.exit, arg, embed_lets,
                        Ssa.Pair(vd, vx), x_access.exit)) in*)
     { eval = s_fragment.eval;
       access = s_fragment.access;
       blocks = proj_block :: case_block :: in_blocks @ s_fragment.blocks}
  | Const _ -> failwith "TODO"
  | Fun((x, xty), s) ->
    let s_fragment =
      lift (Cbvtype.multiplicity t.t_type) (translate s) in
    let y_access = access_of_cbvtype (Ident.fresh "var") s.t_type in
    let x_access = access_of_cbvtype x xty in
    let eval = {
      entry = fresh_label (pair t.t_ann (code_context t.t_context));
      exit  = fresh_label (pair t.t_ann (Cbvtype.code t.t_type)) } in
    let access = access_of_cbvtype (Ident.fresh "fun") t.t_type in
    let eval_block = 
      let arg = Ident.fresh "arg" in
      let tf, tgamma = unPairB eval.entry.Ssa.message_type in
      let stack = Ssa.Fst(Ssa.Var(arg), tf, tgamma) in
      let gamma = Ssa.Snd(Ssa.Var(arg), tf, tgamma) in
      let embed_lets, embed_val =
        embed gamma
          (code_context t.t_context)
          (Cbvtype.code t.t_type) in
      Ssa.Direct(eval.entry, arg,
                 embed_lets,
                 Ssa.Pair(stack, embed_val), eval.exit) in
    let block_decode =
      let te = Cbvtype.multiplicity t.t_type in
      let ta = s.t_ann in
      let td = code_context s.t_context in
      let tcx = Cbvtype.code xty in
      let entry = fresh_label (pair te (pair ta (pair td tcx))) in
      let arg = Ident.fresh "arg" in
      let ve = Ssa.Fst(Ssa.Var(arg), te, pair ta (pair td tcx)) in
      let vadx = Ssa.Snd(Ssa.Var(arg), te, pair ta (pair td tcx)) in
      let va = Ssa.Fst(vadx, ta, pair td tcx) in
      let vdx = Ssa.Snd(vadx, ta, pair td tcx) in
      let vd = Ssa.Fst(vdx, td, tcx) in
      let vx = Ssa.Snd(vdx, td, tcx) in
      let project_lets, project_val =
        project vd (code_context t.t_context) td in
      Ssa.Direct(entry, arg,
                 project_lets,
                 Ssa.Pair(ve, Ssa.Pair(va, Ssa.Pair(project_val, vx))),
                 s_fragment.eval.entry) in
    let case_block =
      let arg = Ident.fresh "arg" in
      let te, tq = unPairB access.entry.Ssa.message_type in
      let td = Cbvtype.code t.t_type in
      let ve = Ssa.Fst(Ssa.Var(arg), te, tq) in
      let req = Ssa.Snd(Ssa.Var(arg), te, tq) in
      let fun_apply = Ident.fresh "apply" in
      let y_entry = Ident.fresh "res_query" in
      let x_exit = Ident.fresh "arg_answer" in
      Ssa.Branch(access.entry, arg, [],
                 (Basetype.Data.sumid 3,
                  [pair td (Cbvtype.code xty);
                   y_access.entry.Ssa.message_type;
                   x_access.exit.Ssa.message_type
                  ],
                  req,
                  [ fun_apply, Ssa.Pair(ve, Ssa.Var fun_apply), Ssa.label_of_block block_decode;
                    y_entry, Ssa.Pair(ve, Ssa.Var y_entry), s_fragment.access.entry;
                    x_exit, Ssa.Pair(ve, Ssa.Var x_exit), x_access.exit
                  ])) in
    let block_in0 =
      let arg = Ident.fresh "arg" in
      Ssa.Direct(s_fragment.eval.exit, arg, [],
                 Ssa.In((Basetype.Data.sumid 3, 0, Ssa.Var arg),
                        access.exit.Ssa.message_type),
                 access.exit) in
    let block_in1 =
      let arg = Ident.fresh "arg" in
      Ssa.Direct(s_fragment.access.exit, arg, [],
                 Ssa.In((Basetype.Data.sumid 3, 1, Ssa.Var arg),
                        access.exit.Ssa.message_type),
                 access.exit) in
    let block_in2 =
      let arg = Ident.fresh "arg" in
      Ssa.Direct(x_access.entry, arg, [],
                 Ssa.In((Basetype.Data.sumid 3, 2, Ssa.Var arg),
                        access.exit.Ssa.message_type),
                 access.exit) in
    { eval = eval;
      access = access;
      blocks = [eval_block; block_decode; case_block; block_in0; block_in1; block_in2]
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

                     (*
      let tu = t.t_ann in
      let tgammadelta = code_context t.t_context in
      let tdelta = code_context t2.t_context in
      let tudelta = pair tu tdelta in
      let arg = Ident.fresh "arg" in
      let vu = Ssa.Fst(Ssa.Var(arg), tu, tgammadelta) in
      let vgammadelta = Ssa.Snd(Ssa.Var(arg), tu, tgammadelta) in
      let vgamma = map_context t.t_context t1.t_context vgammadelta in
      let vdelta = map_context t.t_context t2.t_context vgammadelta in
      let embed_lets, embed_val =
        embed (Ssa.Pair(vu, vdelta)) tudelta t1.t_ann in
      Ssa.Direct(eval.entry, arg,
                 embed_lets,
                 Ssa.Pair(embed_val, vgamma), t1_fragment.eval.entry) in
                      *)
    let block2 =
      let tu = t.t_ann in      
      let teudelta = t1.t_ann in      
      let tdelta = code_context t2.t_context in
      let tudelta = pair tu tdelta in
      let tf = Cbvtype.code t1.t_type in
      let tuf = pair tu tf in
      let teuf = t2.t_ann in
      let arg = Ident.fresh "arg" in
      let veudelta = Ssa.Fst(Ssa.Var(arg), teudelta, tf) in
      let vf = Ssa.Snd(Ssa.Var(arg), teudelta, tf) in
      let project_lets, vudelta = project veudelta tudelta teudelta in
      let vu = Ssa.Fst(vudelta, tu, tdelta) in
      let vdelta = Ssa.Snd(vudelta, tu, tdelta) in
      let vuf = Ssa.Pair(vu, vf) in
      let embed_lets, veuf = embed vuf tuf teuf in
      Ssa.Direct(eval.entry, arg,
                 embed_lets @ project_lets,
                 Ssa.Pair(veuf, vdelta), t2_fragment.eval.entry) in
    let block3 =
      let tu = t.t_ann in      
      let tf = Cbvtype.code t1.t_type in
      let teuf = t2.t_ann in      
      let tx = Cbvtype.code t2.t_type in
      let tuf = pair tu tf in
      let arg = Ident.fresh "arg" in
      let veuf = Ssa.Fst(Ssa.Var(arg), teuf, tx) in
      let vx = Ssa.Snd(Ssa.Var(arg), teuf, tx) in
      let project_lets, vuf = project veuf tuf teuf in
      let vu = Ssa.Fst(vuf, tu, tf) in
      let vf = Ssa.Snd(vuf, tu, tf) in
      Ssa.Direct(eval.entry, arg,
                 project_lets,
                 Ssa.In(
                   (Basetype.Data.sumid 3, 0, Ssa.Pair(vu, Ssa.Pair(vf, vx))),
                   t1_fragment.access.entry.Ssa.message_type),
                 t1_fragment.access.entry) in
    let block5 =
      let tunit = Basetype.newty Basetype.UnitB in
      let td = Cbvtype.multiplicity t1.t_type in
      let embed_lets, veunit = embed Ssa.Unit tunit td in
      let yminus = Ident.fresh "yminus" in
      Ssa.Direct(access.entry, yminus,
                 embed_lets,
                 Ssa.In(
                   (Basetype.Data.sumid 3, 1, Ssa.Pair(veunit, Ssa.Var yminus)),
                   t1_fragment.access.entry.Ssa.message_type),
                 t1_fragment.access.entry) in
    let block7 =
      let tunit = Basetype.newty Basetype.UnitB in
      let td = Cbvtype.multiplicity t1.t_type in
      let embed_lets, veunit = embed Ssa.Unit tunit td in
      let xplus = Ident.fresh "xplus" in
      Ssa.Direct(t2_fragment.access.exit, xplus,
                 embed_lets,
                 Ssa.In(
                   (Basetype.Data.sumid 3, 2, Ssa.Pair(veunit, Ssa.Var xplus)),
                   t1_fragment.access.entry.Ssa.message_type),
                 t1_fragment.access.entry) in
    let case_block =
      let df = Ident.fresh "df" in
      let td = Cbvtype.multiplicity t1.t_type in
      let tf = t1_fragment.access.exit.Ssa.message_type in
      let vf = Ssa.Snd(Ssa.Var(df), td, tf) in
      let res = Ident.fresh "res" in
      let y_exit = Ident.fresh "y_exit" in
      let x_entry = Ident.fresh "x_entry" in
      Ssa.Branch(access.entry, df, [],
                 (Basetype.Data.sumid 3,
                  [ eval.exit.Ssa.message_type;
                    access.exit.Ssa.message_type;
                    t2_fragment.access.entry.Ssa.message_type
                  ],
                  vf,
                  [ res, Ssa.Var res, eval.exit;
                    y_exit, Ssa.Var y_exit, access.exit;
                    x_entry, Ssa.Var x_entry, t1_fragment.access.entry
                  ])) in
    { eval = eval;
      access = access;
      blocks = [block1; block2; block3; block5; block7; case_block]
    }
      
    
  | Ifz(tc, t1, t2) -> failwith "TODO"
