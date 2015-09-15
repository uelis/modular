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

(* TODO: add assertions to check types *)
let end_block_jump (dst: Ssa.label) (v: value) : Ssa.block =
  let vv, va = v in
  match !builder_state with
  | None -> assert false
  | Some s ->
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
     Ssa.Branch(s.cur_label, s.cur_arg, s.cur_lets,
                (id, params, vv, branches))

               
           
let access_entry_type : Cbvtype.t -> Basetype.t =
  failwith "TODO"
           
let access_exit_type : Cbvtype.t -> Basetype.t =
  failwith "TODO"


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
      entry = fresh_label (code_context t.t_context);
      exit  = fresh_label (Cbvtype.code t.t_type) } in
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
       end_block_case vcopy (List.map xs ~f:target) in
     let proj_block =
       let arg = begin_block x_access.entry in
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
             let arg = begin_block y_access.exit in
             let vc = build_fst arg in
             let vx = build_snd arg in
             let vin_c = build_in i vc tsum in
             let td, _ = unPairB x_access.exit.Ssa.message_type in
             let vd = build_embed vin_c td in
             let v = build_pair vd vx in
             end_block_jump x_access.exit v) in
     { eval = s_fragment.eval;
       access = s_fragment.access;
       blocks = proj_block :: case_block :: in_blocks @ s_fragment.blocks}
  | Const _ -> failwith "TODO"
  | Fun((x, xty), s) ->
    let s_fragment =
      lift (Cbvtype.multiplicity t.t_type) (translate s) in
    let x_access = access_of_cbvtype x xty in
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
      let td = code_context s.t_context in
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
      let arg = begin_block s_fragment.eval.exit in
      let ve = build_fst arg in
      let vy = build_snd arg in
      let vy1 = build_in 1 vy tf in
      let v = build_pair ve vy1 in
      end_block_jump access.exit v in
    let block_in2 =
      let te, tf = unPairB access.exit.Ssa.message_type in      
      let arg = begin_block s_fragment.eval.exit in
      let ve = build_fst arg in
      let vy = build_snd arg in
      let vx2 = build_in 2 vy tf in
      let v = build_pair ve vx2 in
      end_block_jump access.exit v in
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
      let vu_f = build_project ve (pair t.t_ann (Cbvtype.code t2.t_type)) in
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
      let v = build_in 1 (build_pair vd arg) tfunacc in
      end_block_jump t1_fragment.access.entry v in
    let block7 =
      let arg = begin_block access.entry in
      let td, tfunacc = unPairB t1_fragment.access.entry.Ssa.message_type in
      let vd = build_embed build_unit td in      
      let v = build_in 2 (build_pair vd arg) tfunacc in
      end_block_jump t1_fragment.access.entry v in
    let case_block =
      let arg = begin_block t1_fragment.access.exit in
      let vfun = build_snd arg in
      end_block_case
        vfun
        [ (fun c -> let v = build_snd c in
                    eval.exit, v);
          (fun c -> let v = build_snd c in
                    access.exit, v);
          (fun c -> let v = build_snd c in
                    t2_fragment.access.entry, v) ] in
    { eval = eval;
      access = access;
      blocks = [block1; block2; block3; block5; block7; case_block]
    }
      
    
  | Ifz(tc, t1, t2) -> failwith "TODO"
