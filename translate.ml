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

let pair: Basetype.t -> Basetype.t -> Basetype.t =
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

let extract_sub_context:
  Cbvtype.t Typing.context -> Cbvtype.t Typing.context -> Ssa.value -> Ssa.value =
  failwith "TODO"

let rec translate (t: Cbvterm.t) : fragment =
  match t.t_desc with
  | Var x ->
    let eval = {
      entry = fresh_label (code_context t.t_context);
      exit  = fresh_label (Cbvtype.code t.t_type) } in
    let access = access_of_cbvtype (Ident.fresh "var") t.t_type in
    let x_access = access_of_cbvtype x t.t_type in
    let block1 = 
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
  | Contr(x, xs) -> failwith "TODO"
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
      let stack = Ssa.Fst(Ssa.Var(arg),
                          t.t_ann,
                          code_context t.t_context) in
      let gamma = Ssa.Snd(Ssa.Var(arg),
                          t.t_ann,
                          code_context t.t_context) in
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
      let te = Cbvtype.multiplicity t.t_type in
      let tq = Cbvtype.code t.t_type in
      let ve = Ssa.Fst(Ssa.Var(arg), te, tq) in
      let req = Ssa.Snd(Ssa.Var(arg), te, tq) in
      let fun_apply = Ident.fresh "apply" in
      let y_entry = Ident.fresh "res_query" in
      let x_exit = Ident.fresh "arg_answer" in
      Ssa.Branch(access.entry, arg, [],
                 (Basetype.Data.sumid 3,
                  [Basetype.newty
                     (Basetype.PairB(code_context t.t_context,
                                     Cbvtype.code xty));
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
      let tu = t.t_ann in
      let tgammadelta = code_context t.t_context in
      let tdelta = code_context t2.t_context in
      let tudelta = pair tu tdelta in
      let arg = Ident.fresh "arg" in
      let vu = Ssa.Fst(Ssa.Var(arg), tu, tgammadelta) in
      let vgammadelta = Ssa.Snd(Ssa.Var(arg), tu, tgammadelta) in
      let vgamma = extract_sub_context t.t_context t1.t_context vgammadelta in
      let vdelta = extract_sub_context t.t_context t2.t_context vgammadelta in
      let embed_lets, embed_val =
        embed (Ssa.Pair(vu, vdelta)) tudelta t1.t_ann in
      Ssa.Direct(eval.entry, arg,
                 embed_lets,
                 Ssa.Pair(embed_val, vgamma), t1_fragment.eval.entry) in
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
      Ssa.Direct(t2_fragment.access.exit, arg,
                 embed_lets,
                 Ssa.In(
                   (Basetype.Data.sumid 3, 2, Ssa.Pair(veunit, Ssa.Var xplus)),
                   t1_fragment.access.entry.Ssa.message_type),
                 t1_fragment.access.entry) in
      
    
  | Ifz(tc, t1, t2) -> failwith "TODO"
