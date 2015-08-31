open Core.Std
open Cbvterm

module Ident = Intlib.Ident
module Basetype = Intlib.Basetype
module Ssa = Intlib.Ssa               

type fragment = {
    entry: Ssa.label list;
    blocks: Ssa.block list;
    exit: Ssa.label list
  }

let fresh_label : Basetype.t -> Ssa.label =
  let next_label = ref 0 in
  fun a ->
  let i = !next_label in
  incr next_label;
  {Ssa.name = i;
   Ssa.message_type = a }

let translate (t: Cbvterm.t) : fragment =
  match t.t_desc with
  | Var x -> failwith "TODO"
  | Contr _ -> failwith "TODO"
  | Const _ -> failwith "TODO"
  | Fun(x, s) -> failwith "TODO"
  | Fix((f, x, alpha), s) -> failwith "TODO"
  | App(t1, t2) -> failwith "TODO"
  | Ifz(tc, t1, t2) -> failwith "TODO"
