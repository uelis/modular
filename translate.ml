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

type interface = {
  access_entry: Ssa.label;
  access_exit: Ssa.label;
  eval_entry: Ssa.label;
  eval_exit: Ssa.label
}

let access_of_cbvtype : Ident.t -> Cbvtype.t -> int_interface =
  failwith "TODO"
    
let value_type_of_cbvtype : Cbvtype.t -> Basetype.t =
  failwith "TODO"

let value_type_of_context : Cbvtype.t Typing.context -> Basetype.t =
  failwith "TODO"

let projection: Cbvtype.t Typing.context -> Ident.t -> Ssa.value =
  failwith "TODO"

let rec translate (t: Cbvterm.t) : fragment =
  match t.t_desc with
  | Var x ->
    let eval = {
      entry = fresh_label (value_type_of_context t.t_context);
      exit  = fresh_label (value_type_of_cbvtype t.t_type) } in
    let access = access_of_cbvtype (Ident.fresh "var") t.t_type in
    let x_access = access_of_cbvtype x t.t_type in
    let block1 =
      let arg = Ident.fresh "arg" in
      Ssa.Direct(access.entry, arg, [],
                 Ssa.Var arg, x_access.entry) in
    let block2 =
      let arg = Ident.fresh "arg" in
      Ssa.Direct(x_access.exit, arg, [],
                 Ssa.Var arg, x_access.exit) in
    let eval_block = 
      let arg = Ident.fresh "gamma" in
      let rec proj gamma v =
        match gamma with
        | [] -> assert false
        | (y, a) :: delta ->
          if x = y then
            Ssa.Snd(v, value_type_of_context delta, value_type_of_cbvtype a)
          else
            let v' = Ssa.Fst(v, value_type_of_context delta,
                             value_type_of_cbvtype a) in
            proj delta v' in
      Ssa.Direct(eval.entry, arg, [],
                 proj t.t_context (Ssa.Var x), eval.exit) in
    { eval = eval;
      access = access;
      blocks = [eval_block; block1; block2]
    }
  | Contr(x, xs) -> failwith "TODO"
  | Const _ -> failwith "TODO"
  | Fun((x, a), s) ->
    let s_fragment = translate s in
    let res_access = access_of_cbvtype (Ident.fresh "var") s.t_type in
    let arg_access = access_of_cbvtype x a in
    let eval = {
      entry = fresh_label (value_type_of_context t.t_context);
      exit  = fresh_label (value_type_of_cbvtype t.t_type) } in
    let access = access_of_cbvtype (Ident.fresh "fun") t.t_type in
    let x_access = access_of_cbvtype x a in
    let block1 =
      let arg = Ident.fresh "arg" in
      let fun_apply = Ident.fresh "apply" in
      let res_entry = Ident.fresh "res_query" in
      let arg_exit = Ident.fresh "arg_answer" in
      Ssa.Branch(access.entry, arg, [],
                 (Basetype.Data.sumid 3,
                  [Basetype.newty
                     (Basetype.PairB(value_type_of_context t.t_context,
                                     value_type_of_cbvtype a));
                   res_access.entry.Ssa.message_type;
                   arg_access.exit.Ssa.message_type
                  ],
                  Ssa.Var arg,
                  [ fun_apply, Ssa.Var fun_apply, s_fragment.eval.entry;
                    res_entry, Ssa.Var res_entry, s_fragment.access.entry;
                    arg_exit, Ssa.Var arg_exit, x_access.exit
                  ])) in
    let access_exit_type = 
      Basetype.newty
        (Basetype.DataB (
           Basetype.Data.sumid 3,
           [value_type_of_cbvtype s.t_type;
            res_access.exit.Ssa.message_type;
            arg_access.entry.Ssa.message_type
           ])) in
    let block2 =
      let arg = Ident.fresh "arg" in
      Ssa.Direct(s_fragment.eval.exit, arg, [],
                 Ssa.In((Basetype.Data.sumid 3, 0, Ssa.Var arg),
                        access_exit_type),
                 access.exit) in
    let block3 =
      let arg = Ident.fresh "arg" in
      Ssa.Direct(s_fragment.access.exit, arg, [],
                 Ssa.In((Basetype.Data.sumid 3, 1, Ssa.Var arg),
                        access_exit_type),
                 access.exit) in
    let block4 =
      let arg = Ident.fresh "arg" in
      Ssa.Direct(x_access.entry, arg, [],
                 Ssa.In((Basetype.Data.sumid 3, 2, Ssa.Var arg),
                        access_exit_type),
                 access.exit) in
    let eval_block = 
      let gamma = Ident.fresh "gamma" in
      Ssa.Direct(eval.entry, gamma, [], Ssa.Var gamma, eval.exit) in
    { eval = eval;
      access = access;
      blocks = [eval_block; block1; block2; block3; block4]
    }
  | Fix((f, x, alpha), s) -> failwith "TODO"
  | App(t1, t2) -> failwith "TODO"
  | Ifz(tc, t1, t2) -> failwith "TODO"
