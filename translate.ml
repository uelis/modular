open Core.Std
open Cbvterm

module Ident = Intlib.Ident
module Basetype = Intlib.Basetype
module Ssa = Intlib.Ssa               
module Intast = Intlib.Ast
module Builder = Ssabuilder
               
type int_interface = {
  entry: Ssa.label;
  exit: Ssa.label
}

type fragment = {
    eval: int_interface;
    access: int_interface;
    blocks: Ssa.block list;
    context: (Ident.t * int_interface) list
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
                
let rec code_context (gamma : Cbvtype.t Typing.context) : Basetype.t =
  match gamma with
  | [] -> Basetype.newty Basetype.UnitB
  | (_, a) :: delta ->
     pair (code_context delta) (Cbvtype.code a )
           
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
        let yexit = access_exit_type y in
        let xentry = access_entry_type x in
        let sumid = Basetype.Data.sumid 3 in
        let params = [pair s yc; yexit; xentry] in
        let sum = Basetype.newty (Basetype.DataB(sumid, params)) in
        pair m sum
          
let fresh_label (name: string) (a : Basetype.t): Ssa.label =
  { Ssa.name = Ident.fresh name;
    Ssa.message_type = a }
     
let fresh_eval (s: string) (t: Cbvterm.t) : int_interface =
  { entry = fresh_label (s ^ "_eval_entry") (pair t.t_ann (code_context t.t_context));
    exit  = fresh_label (s ^ "_eval_exit") (pair t.t_ann (Cbvtype.code t.t_type)) }

let fresh_access (s: string) (a: Cbvtype.t) : int_interface =
  { entry = fresh_label (s ^ "_access_entry") (access_entry_type a);
    exit = fresh_label (s ^ "_access_entry") (access_exit_type a)
  }
          
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
    blocks = List.map ~f:lift_block f.blocks;
    access = lift_int_interface a f.access;
    context = List.map ~f:(fun (x, i) -> (x, lift_int_interface a i))
                f.context
  }

let rec build_context_lookup
          (gamma: Cbvtype.t Typing.context)
          (x: Ident.t)
          (v: Builder.value)
  : Builder.value =
  match gamma with
  | [] -> assert false
  | (y, a) :: delta ->
     if x = y then
       Builder.snd v
    else
      let v' = Builder.fst v in
      build_context_lookup delta x v' 

let build_context_map
      (gamma: Cbvtype.t Typing.context)
      (delta: Cbvtype.t Typing.context)
      (code_gamma: Builder.value)
    : Builder.value =
  let rec values gamma code_gamma =
    match gamma with
    | [] -> []
    | (x, a) :: gamma' ->
       let code_gamma', code_x = Builder.unpair code_gamma in
       (x, code_x) :: (values gamma' code_gamma') in
  let gamma_values = values gamma code_gamma in
  let delta_values =
    List.map
      ~f:(fun (x, _) -> (x, List.Assoc.find_exn gamma_values x))
      delta in
  let v = List.fold_right delta_values
                          ~init:Builder.unit
                          ~f:(fun (x, vx) v -> Builder.pair v vx) in
  v

let print_context c =
  List.iter c
    ~f:(fun (x, a) ->
     Printf.printf "%s:%s, "
                   (Ident.to_string x)
                   (Cbvtype.to_string ~concise:false a));
  Printf.printf "\n"
                
let print_fcontext c =
  List.iter c
    ~f:(fun (x, a) ->
     Printf.printf "%s:(%s, %s), "
                   (Ident.to_string x)
                   (Intlib.Printing.string_of_basetype a.entry.Ssa.message_type)
                   (Intlib.Printing.string_of_basetype a.exit.Ssa.message_type)
       );
  Printf.printf "\n"

(* TODO: spec *)
let rec embed_context outer gamma =
  match gamma with
  | [] -> [], []
  | (y, y_access) :: gamma'  ->
    let outer_gamma', blocks = embed_context outer gamma' in
    let y_outer_access = fresh_access "context_embed"
                           (List.Assoc.find_exn outer.t_context y) in
    let tstack_outer, _ = unPairB y_outer_access.entry.Ssa.message_type in
    let _, tminner = unPairB y_access.entry.Ssa.message_type in
    let tstack_inner, _ = unPairB tminner in
           (*
       let yty_inner = List.Assoc.find_exn s.t_context y in
       Printf.printf "%s(%s), %s(%s)\n%!"
       (Cbvtype.to_string ~concise:false yty_outer)
       (Intlib.Printing.string_of_basetype tstack_outer)
       (Cbvtype.to_string ~concise:false yty_inner)
       (Intlib.Printing.string_of_basetype tstack_inner);
    *)
    let exit_block =
      let arg = Builder.begin_block y_outer_access.exit in
      let vstack_outer, vm = Builder.unpair arg in
      let vstack_pair = Builder.project vstack_outer
                          (pair (Cbvtype.multiplicity outer.t_type) tstack_inner) in
      let ve, vstack_inner = Builder.unpair vstack_pair in
      let v = Builder.pair ve (Builder.pair vstack_inner vm) in
      Builder.end_block_jump y_access.exit v in
    let entry_block =
      let arg = Builder.begin_block y_access.entry in
      let ve, vpair = Builder.unpair arg in
      let vstack_inner, vm = Builder.unpair vpair in
      let vstack_outer = Builder.embed (Builder.pair ve vstack_inner) tstack_outer in
      let v = Builder.pair vstack_outer vm in
      Builder.end_block_jump y_outer_access.entry v in
    (y, y_outer_access) :: outer_gamma',
    [entry_block; exit_block] @ blocks 


let rec translate (t: Cbvterm.t) : fragment =
  match t.t_desc with
  | Var x ->
     Printf.printf "Var %s\n%!"
       (Cbvtype.to_string ~concise:false t.t_type);
     let id = "var" in
     let eval = fresh_eval id t in
     let access = fresh_access id t.t_type in
     let x_access = fresh_access id t.t_type in
     let eval_block =
       let arg = Builder.begin_block eval.entry in
       let va, vgamma = Builder.unpair arg in
       let vx = build_context_lookup t.t_context x vgamma in
       let v = Builder.pair va vx in
       Builder.end_block_jump eval.exit v in
     let access_block =
       let arg = Builder.begin_block access.entry in
       Builder.end_block_jump x_access.entry arg in
     let x_access_exit_block =
       let arg = Builder.begin_block x_access.exit in
       Builder.end_block_jump access.exit arg in
     { eval = eval;
       access = access;
       blocks = [eval_block; access_block; x_access_exit_block];
       context = [(x, x_access)]
     }
  | Contr((x, xs), s) ->
     let s_fragment = translate s in
     print_context s.t_context;
     print_fcontext s_fragment.context;
     let id = "contr" in
     let eval = {
       entry = fresh_label (id ^ "_eval_entry")
                 (pair t.t_ann (code_context t.t_context));
       exit = s_fragment.eval.exit
     } in
     let x_access = fresh_access "contr"
                      (List.Assoc.find_exn t.t_context x) in
     let tsum =
       let summands = List.map xs
                        ~f:(fun x' -> Cbvtype.multiplicity
                                        (List.Assoc.find_exn s.t_context x')) in
       let sumid = Basetype.Data.sumid (List.length summands) in
       Basetype.newty (Basetype.DataB(sumid, summands)) in
     Printf.printf "X+: %s\n"
       (Intlib.Printing.string_of_basetype x_access.exit.Ssa.message_type);
     let eval_block =
       let arg = Builder.begin_block eval.entry in
       let vstack, vgamma = Builder.unpair arg in
       let delta =
         List.map s.t_context
           ~f:(fun (y, a) -> (if List.mem xs y then x else y), a) in
       let vdelta = build_context_map t.t_context delta vgamma in
       let v = Builder.pair vstack vdelta in
       Builder.end_block_jump s_fragment.eval.entry v in
     let proj_block =
       let arg = Builder.begin_block x_access.exit in
       let vd, vx = Builder.unpair arg in
       let vsum = Builder.project vd tsum in
       let target y =
         fun c -> let y_access = List.Assoc.find_exn s_fragment.context y in
                  let v = Builder.pair c vx in
                  y_access.exit, v in
       Builder.end_block_case vsum (List.map xs ~f:target) in
     let inj_blocks =
       List.mapi xs
         ~f:(fun i y ->
             let y_access = List.Assoc.find_exn s_fragment.context y in
             let arg = Builder.begin_block y_access.entry in
             let vc, vx = Builder.unpair arg in
             let vin_c = Builder.inj i vc tsum in
             let td, _ = unPairB x_access.entry.Ssa.message_type in
             let vd = Builder.embed vin_c td in
             let v = Builder.pair vd vx in
             Builder.end_block_jump x_access.entry v) in
     { eval = eval;
       access = s_fragment.access;
       blocks = eval_block :: proj_block :: inj_blocks @ s_fragment.blocks;
       context = (x, x_access) ::
                 (List.filter s_fragment.context
                    ~f:(fun (x, a) -> not (List.mem xs x)))
     }
  | Const(Ast.Cintconst i, []) ->
    let id = "intconst" in
    let eval = fresh_eval id t in
    let access = fresh_access id t.t_type in
    let eval_block =
      let arg = Builder.begin_block eval.entry in
      let vstack = Builder.fst arg in
      let vi = Builder.intconst i in
      let v = Builder.pair vstack vi in
      Builder.end_block_jump eval.exit v in
    let access_block =
      let arg = Builder.begin_block access.entry in
      Builder.end_block_jump access.exit arg in
    { eval = eval;
      access = access;
      blocks = [eval_block; access_block];
      context = []
    }
  | Const(Ast.Cintconst i, _) ->
     assert false
  | Const(Ast.Cintprint, [s]) ->
     Printf.printf "Print %s\n%!"
                   (Cbvtype.to_string ~concise:false t.t_type);
     let s_fragment = translate s in
     let id = "intprint" in
     let eval = fresh_eval id t in
     let access = fresh_access id t.t_type in
     let eval_block =
       let arg = Builder.begin_block eval.entry in
       Builder.end_block_jump s_fragment.eval.entry arg in
     let print_block =
       let arg = Builder.begin_block s_fragment.eval.exit in
       let vi = Builder.snd arg in
       ignore (Builder.primop (Intast.Cintprint) vi);
       Builder.end_block_jump eval.exit arg in
    let access_entry_block =
       let arg = Builder.begin_block access.entry in
       Builder.end_block_jump access.exit arg in
    let access_exit_block =
       let arg = Builder.begin_block s_fragment.access.exit in
       Builder.end_block_jump s_fragment.access.exit arg in
    { eval = eval;
      access = access;
      blocks = [eval_block; print_block;
                access_entry_block; access_exit_block]
               @ s_fragment.blocks;
      context = s_fragment.context
    }
  | Const(Ast.Cintprint, _) ->
     assert false
  | Const(Ast.Cintadd, [s1; s2]) ->
     let s1_fragment = translate s1 in
     let s2_fragment = translate s2 in
     let id = "intadd" in
     let eval = fresh_eval id t in
     let access = fresh_access id t.t_type in
     let eval_block1 =
       let arg = Builder.begin_block eval.entry in
       let vstack, vgamma = Builder.unpair arg in
       let vgamma1 = build_context_map t.t_context s1.t_context vgamma in
       let vgamma2 = build_context_map t.t_context s2.t_context vgamma in
       let vstack1 = Builder.embed (Builder.pair vstack vgamma2) s1.t_ann in
       let v = Builder.pair vstack1 vgamma1 in
       Builder.end_block_jump s1_fragment.eval.entry v in
     let eval_block2 =
       let arg = Builder.begin_block s1_fragment.eval.exit in
       let vstack1, vn1 = Builder.unpair arg in
       let vp = Builder.project vstack1
                  (pair t.t_ann (code_context s2.t_context)) in
       let vstack, vgamma2 = Builder.unpair vp in
       let vstack2 = Builder.embed (Builder.pair vstack vn1) s2.t_ann in
       let v = Builder.pair vstack2 vgamma2 in
       Builder.end_block_jump s2_fragment.eval.entry v in
     let eval_block3 =
       let arg = Builder.begin_block s2_fragment.eval.exit in
       let vstack2, vn2 = Builder.unpair arg in
       let vp = Builder.project vstack2 (pair t.t_ann intB) in
       let vstack, vn1 = Builder.unpair vp in
       let vsum = Builder.primop (Intast.Cintadd) (Builder.pair vn1 vn2) in
       let v = Builder.pair vstack vsum in
       Builder.end_block_jump eval.exit v in
    let access_block =
      let arg = Builder.begin_block access.entry in
      Builder.end_block_jump access.exit arg in
    (* dummy blocks *)
    let access_block1 =
      let arg = Builder.begin_block s1_fragment.access.exit in
      Builder.end_block_jump s1_fragment.access.exit arg in
    let access_block2 =
      let arg = Builder.begin_block s2_fragment.access.exit in
      Builder.end_block_jump s2_fragment.access.exit arg in
    { eval = eval;
      access = access;
      blocks = [eval_block1; eval_block2; eval_block3;
                access_block; access_block1; access_block2]
               @ s1_fragment.blocks
               @ s2_fragment.blocks;
      context = s1_fragment.context @ s2_fragment.context
    }
  | Const(Ast.Cintadd, _) ->
     assert false
  | Fun((x, xty), s) ->
    let s_fragment = lift (Cbvtype.multiplicity t.t_type) (translate s) in
    print_context s.t_context;
    print_fcontext s_fragment.context;
    let id = "fun" in
    let eval = fresh_eval id t in
    let access = fresh_access id t.t_type in
    (* TODO: nimmt an, dass x im context von s vorkommt. *)
    let x_access = List.Assoc.find_exn s_fragment.context x in
    let eval_block =
      let arg = Builder.begin_block eval.entry in
      let vstack, vgamma = Builder.unpair arg in
      let vclosure = Builder.embed vgamma (Cbvtype.code t.t_type) in
      let v = Builder.pair vstack vclosure in
      Builder.end_block_jump eval.exit v in
    let invoke_block =
      let te = Cbvtype.multiplicity t.t_type in
      let ta = s.t_ann in
      (*
      Printf.printf "Ann: %s, %s\n"
                    (Intlib.Printing.string_of_basetype ta)
                    (Cbvtype.to_string ~concise:false t.t_type);
       *)
      let td = Cbvtype.code t.t_type in
      let tcx = Cbvtype.code xty in
      let entry = fresh_label "fun_decode" (pair te (pair ta (pair td tcx))) in
      let arg = Builder.begin_block entry in
      let ve, vadx = Builder.unpair arg in
      let va, vdx = Builder.unpair vadx in
      let vd, vx = Builder.unpair vdx in
      let vgamma = Builder.project vd (code_context t.t_context) in
      let vgammax = Builder.pair vgamma vx in
      let vdelta = build_context_map ((x, xty)::t.t_context) s.t_context vgammax in
      (* TODO: Dokumentieren! *)
      let v = Builder.pair ve (Builder.pair va vdelta) in
      Builder.end_block_jump s_fragment.eval.entry v in
    let access_block =
      let arg = Builder.begin_block access.entry in
      let ve = Builder.fst arg in
      let vreq = Builder.snd arg in
      Builder.end_block_case
        vreq
        [(fun c -> let v = Builder.pair ve c in
                   Ssa.label_of_block invoke_block, v);
         (fun c -> let v = Builder.pair ve c in
                   s_fragment.access.entry, v);
         (fun c -> let v = Builder.pair ve c in
                   x_access.exit, v)] in
    let s_eval_exit_block =
      let arg = Builder.begin_block s_fragment.eval.exit in
      let _, tf = unPairB access.exit.Ssa.message_type in
      let ve, vv = Builder.unpair arg in
      let vv0 = Builder.inj 0 vv tf in
      let v = Builder.pair ve vv0 in
      Builder.end_block_jump access.exit v in
    let s_access_exit_block =
      let arg = Builder.begin_block s_fragment.access.exit in
      let te, tf = unPairB access.exit.Ssa.message_type in      
      let ve, vy = Builder.unpair arg in
      let vy1 = Builder.inj 1 vy tf in
      let v = Builder.pair ve vy1 in
      Builder.end_block_jump access.exit v in
    let s_x_access_entry_block =
      let arg = Builder.begin_block x_access.entry in
      let te, tf = unPairB access.exit.Ssa.message_type in      
      let ve, vy = Builder.unpair arg in
      let vx2 = Builder.inj 2 vy tf in
      let v = Builder.pair ve vx2 in
      Builder.end_block_jump access.exit v in
    (*
    let rec embed_context gamma =
      match gamma with
      | [] -> [], []
      | (y, y_access) :: gamma'  ->
         let outer_gamma', blocks = embed_context gamma' in
         if x = y then
           outer_gamma', blocks
         else
           let y_outer_access = fresh_access "context_embed"
                                  (List.Assoc.find_exn t.t_context y) in
           let tstack_outer, _ = unPairB y_outer_access.entry.Ssa.message_type in
           let _, tminner = unPairB y_access.entry.Ssa.message_type in
           let tstack_inner, _ = unPairB tminner in
           (*
           let yty_inner = List.Assoc.find_exn s.t_context y in
           Printf.printf "%s(%s), %s(%s)\n%!"
                         (Cbvtype.to_string ~concise:false yty_outer)
                         (Intlib.Printing.string_of_basetype tstack_outer)
                         (Cbvtype.to_string ~concise:false yty_inner)
                         (Intlib.Printing.string_of_basetype tstack_inner);
           *)
           let exit_block =
             let arg = Builder.begin_block y_outer_access.exit in
             let vstack_outer, vm = Builder.unpair arg in
             let vstack_pair = Builder.project vstack_outer
                                 (pair (Cbvtype.multiplicity t.t_type) tstack_inner) in
             let ve, vstack_inner = Builder.unpair vstack_pair in
             let v = Builder.pair ve (Builder.pair vstack_inner vm) in
             Builder.end_block_jump y_access.exit v in
           let entry_block =
             let arg = Builder.begin_block y_access.entry in
             let ve, vpair = Builder.unpair arg in
             let vstack_inner, vm = Builder.unpair vpair in
             let vstack_outer = Builder.embed (Builder.pair ve vstack_inner) tstack_outer in
             let v = Builder.pair vstack_outer vm in
             Builder.end_block_jump y_outer_access.entry v in
           (y, y_outer_access) :: outer_gamma',
           [entry_block; exit_block] @ blocks in
    let context, context_blocks = embed_context s_fragment.context in
    *)
    let context, context_blocks =
      let gamma = List.filter s_fragment.context ~f:(fun (y, _) -> x <> y) in
      embed_context t gamma in
    { eval = eval;
      access = access;
      blocks = [eval_block; access_block; invoke_block;
                s_eval_exit_block; s_access_exit_block; s_x_access_entry_block]
               @ context_blocks
               @ s_fragment.blocks;
      context = context
    }
  | Fix((th, f, x, xty), s) ->
     Printf.printf "Fix: %s\n" (Cbvtype.to_string ~concise:false t.t_type);
     let s_fragment = lift th (translate s) in
     let id = "fix" in
     let eval = fresh_eval id t in
     let access = fresh_access id t.t_type in
     let x_access = List.Assoc.find_exn s_fragment.context x in
     let f_access = List.Assoc.find_exn s_fragment.context f in
     print_context s.t_context;
     print_fcontext s_fragment.context;
     (* E + H *G *)
     let te = Cbvtype.multiplicity t.t_type in
     let tg = Cbvtype.multiplicity (List.Assoc.find_exn s.t_context f) in
     let thg = pair th tg in
     let tcons =
       Basetype.newty (Basetype.DataB(Basetype.Data.sumid 2, [te; thg])) in
     let build_singleton ve =
       Builder.embed (Builder.inj 0 ve tcons) th in
     let build_push vh vg =
       Builder.embed (Builder.inj 1 (Builder.pair vh vg) tcons) th in
     let eval_block =
       let arg = Builder.begin_block eval.entry in
       let vstack, vgamma = Builder.unpair arg in
       let vclosure = Builder.embed vgamma (Cbvtype.code t.t_type) in
       let v = Builder.pair vstack vclosure in
       Builder.end_block_jump eval.exit v in
     let eval_body_block =
       let ta = s.t_ann in
       let td = Cbvtype.code t.t_type in
       let tx = Cbvtype.code xty in
       let arg = Builder.begin_block
                   (fresh_label (id ^ "eval_body")
                      (pair th (pair ta (pair td tx)))) in
       let vh, vadx = Builder.unpair arg in
       let va, vdx = Builder.unpair vadx in
       let vd, vx = Builder.unpair vdx in
       let vgamma = Builder.project vd (code_context t.t_context) in
       let vgammadx = Builder.pair (Builder.pair vgamma vd) vx in
       let vdelta = build_context_map
                      ((x, xty)::(f, t.t_type)::t.t_context) s.t_context vgammadx in
       let v = Builder.pair vh (Builder.pair va vdelta) in
       Builder.end_block_jump s_fragment.eval.entry v in
     let access_block =
       let arg = Builder.begin_block access.entry in
       let ve, vreq = Builder.unpair arg in
       let vh = build_singleton ve in
       Builder.end_block_case
         vreq
         [ (fun c -> Ssa.label_of_block eval_body_block, Builder.pair vh c);
           (fun c -> s_fragment.access.entry, Builder.pair vh c);
           (fun c -> x_access.exit, Builder.pair vh c) ] in
     let invoke_rec_block =
       let _(*th*), t1 = unPairB f_access.exit.Ssa.message_type in
       let _(*tg*), tans = unPairB t1 in
       let arg = Builder.begin_block
                   (fresh_label (id ^ "invoke_rec") (pair thg tans)) in
       let vhg, vm = Builder.unpair arg in
       let vh, vg = Builder.unpair vhg in
       let v = Builder.pair vh (Builder.pair vg vm) in
       Builder.end_block_jump f_access.exit v in
     let s_eval_exit_block =
       let arg = Builder.begin_block s_fragment.eval.exit in
       let vh, vm = Builder.unpair arg in
       let _, ta = unPairB access.exit.Ssa.message_type in
       let vm0 = Builder.inj 0 vm ta in
       let vcons = Builder.project vh tcons in
       Builder.end_block_case
         vcons
         [ (fun ve ->
            access.exit, Builder.pair ve vm0);
           (fun vhg ->
            Ssa.label_of_block invoke_rec_block, Builder.pair vhg vm0)
         ] in
     let s_access_exit_block =
       let arg = Builder.begin_block s_fragment.access.exit in
       let vh, vm = Builder.unpair arg in
       let _, ta = unPairB access.exit.Ssa.message_type in
       let vm1 = Builder.inj 1 vm ta in
       let vcons = Builder.project vh tcons in
       Builder.end_block_case
         vcons
         [ (fun ve ->
            access.exit, Builder.pair ve vm1);
           (fun vhg ->
            Ssa.label_of_block invoke_rec_block, Builder.pair vhg vm1)
         ] in
     let x_access_entry_block =
       let arg = Builder.begin_block x_access.entry in
       let vh = Builder.fst arg in
       let vm = Builder.snd arg in
       let _, ta = unPairB access.exit.Ssa.message_type in
       let vm2 = Builder.inj 2 vm ta in
       let vcons = Builder.project vh tcons in
       Builder.end_block_case
         vcons
         [ (fun ve ->
            access.exit, Builder.pair ve vm2);
           (fun vhg ->
            Ssa.label_of_block invoke_rec_block, Builder.pair vhg vm2)
         ] in
     let f_access_entry_block =
       let arg = Builder.begin_block f_access.entry in
       let vh, vgm = Builder.unpair arg in
       let vg, vm = Builder.unpair vgm in
       let vpushed = build_push vh vg in
       Builder.end_block_case
         vm
         [ (fun c -> Ssa.label_of_block eval_body_block, Builder.pair vpushed c);
           (fun c -> s_fragment.access.entry, Builder.pair vpushed c);
           (fun c -> x_access.exit, Builder.pair vpushed c)
         ] in
     (*
     let rec embed_context gamma =
       match gamma with
       | [] -> [], []
       | (y, y_access) :: gamma'  ->
          let outer_gamma', blocks = embed_context gamma' in
          if x = y || f = y then
            outer_gamma', blocks
          else
            let te = Cbvtype.multiplicity t.t_type in
            let yty_outer = List.Assoc.find_exn t.t_context y in
            let yty_inner = List.Assoc.find_exn s.t_context y in
            let y_outer_access = fresh_access "context_embed" yty_outer in
            let tstack_outer, _ = unPairB y_outer_access.entry.Ssa.message_type in
            let _, tminner = unPairB y_access.entry.Ssa.message_type in
            let tstack_inner, _ = unPairB tminner in
            Printf.printf "%s(%s), %s(%s)\n%!"
                          (Cbvtype.to_string ~concise:false yty_outer)
                          (Intlib.Printing.string_of_basetype tstack_outer)
                          (Cbvtype.to_string ~concise:false yty_inner)
                          (Intlib.Printing.string_of_basetype tstack_inner);
            let exit_block =
              let arg = Builder.begin_block y_outer_access.exit in
              let vstack_outer, vm = Builder.unpair arg in
              let vstack_pair = Builder.project vstack_outer (pair te tstack_inner) in
              let ve, vstack_inner = Builder.unpair vstack_pair in
              let v = Builder.pair ve (Builder.pair vstack_inner vm) in
              Builder.end_block_jump y_access.exit v in
            let entry_block =
              let arg = Builder.begin_block y_access.entry in
              let ve, vpair = Builder.unpair arg in
              let vstack_inner, vm = Builder.unpair vpair in
              let vstack_outer = Builder.embed (Builder.pair ve vstack_inner) tstack_outer in
              let v = Builder.pair vstack_outer vm in
              Builder.end_block_jump y_outer_access.entry v in
            (y, y_outer_access) :: outer_gamma',
            [entry_block; exit_block] @ blocks in
     let context, context_blocks = embed_context s_fragment.context in
     *)
    let context, context_blocks =
      let gamma = List.filter s_fragment.context
                    ~f:(fun (y, _) -> y <> x && y <> f) in
      embed_context t gamma in
     { eval = eval;
       access = access;
       blocks = [eval_block; access_block; eval_body_block; invoke_rec_block;
                 s_eval_exit_block; s_access_exit_block; x_access_entry_block;
                 f_access_entry_block]
                @ context_blocks
                @ s_fragment.blocks;
      context = context
    }
  | App(t1, t2) ->
    let t1_fragment = translate t1 in
    let t2_fragment = translate t2 in
    let id = "app" in
    let eval = fresh_eval id t in
    let access = fresh_access id t.t_type in
    Printf.printf "App: %s\n" (Cbvtype.to_string ~concise:false t1.t_type);
    let block1 =
      let arg = Builder.begin_block eval.entry in
      let vu, vgammadelta = Builder.unpair arg in
      let vgamma = build_context_map t.t_context t1.t_context vgammadelta in
      let vdelta = build_context_map t.t_context t2.t_context vgammadelta in
      let embed_val = Builder.embed (Builder.pair vu vdelta) t1.t_ann in
      let v = Builder.pair embed_val vgamma in
      Builder.end_block_jump t1_fragment.eval.entry v in
    let block2 =
      let arg = Builder.begin_block t1_fragment.eval.exit in
      let ve, vf = Builder.unpair arg in
      let vu_delta = Builder.project ve
                       (pair t.t_ann (code_context t2.t_context)) in
      let vu, vdelta = Builder.unpair vu_delta in
      let vu_f = Builder.pair vu vf in
      let ve' = Builder.embed vu_f t2.t_ann in
      let v = Builder.pair ve' vdelta in
      Builder.end_block_jump t2_fragment.eval.entry v in
    let block3 =
      let arg = Builder.begin_block t2_fragment.eval.exit in
      let ve, vx = Builder.unpair arg in
      let vu_f = Builder.project ve (pair t.t_ann (Cbvtype.code t1.t_type)) in
      let vu, vf = Builder.unpair vu_f in
      let vufx = Builder.pair vu (Builder.pair vf vx) in
      let td, tfunacc = unPairB t1_fragment.access.entry.Ssa.message_type in
      let vfunacc = Builder.inj 0 vufx tfunacc in
      let vd = Builder.embed Builder.unit td in
      let v = Builder.pair vd vfunacc in
      Builder.end_block_jump t1_fragment.access.entry v in
    let block5 =
      let arg = Builder.begin_block access.entry in
      let td, tfunacc = unPairB t1_fragment.access.entry.Ssa.message_type in
      let vd = Builder.embed Builder.unit td in      
      let v = Builder.pair vd (Builder.inj 1 arg tfunacc) in
      Builder.end_block_jump t1_fragment.access.entry v in
    let block7 =
      let arg = Builder.begin_block t2_fragment.access.exit in
      let td, tfunacc = unPairB t1_fragment.access.entry.Ssa.message_type in
      let vd = Builder.embed Builder.unit td in      
      let v = Builder.pair vd (Builder.inj 2 arg tfunacc) in
      Builder.end_block_jump t1_fragment.access.entry v in
    let case_block =
      let arg = Builder.begin_block t1_fragment.access.exit in
      let vfun = Builder.snd arg in
      Builder.end_block_case
        vfun
        [ (fun c -> eval.exit, c);
          (fun c -> access.exit, c);
          (fun c -> t2_fragment.access.entry, c) ] in
    { eval = eval;
      access = access;
      blocks = [block1; block2; block3; block5; block7; case_block]
               @ t1_fragment.blocks
               @ t2_fragment.blocks;
      context = t1_fragment.context @ t2_fragment.context
    }
  | Ifz(tc, t1, t2) -> 
     let tc_fragment = translate tc in
     let t1_fragment = translate t1 in
     let t2_fragment = translate t2 in
     let id = "if" in
     let eval = fresh_eval id t in
     let access = fresh_access id t.t_type in
     let eval_block1 =
       let arg = Builder.begin_block eval.entry in
       let vstack, vgamma = Builder.unpair arg in
       let vgammac = build_context_map t.t_context tc.t_context vgamma in
       let vgamma1 = build_context_map t.t_context t1.t_context vgamma in
       let vgamma2 = build_context_map t.t_context t2.t_context vgamma in
       let vstack1 = Builder.embed (Builder.pair vstack (Builder.pair vgamma1 vgamma2)) tc.t_ann in
       let v = Builder.pair vstack1 vgammac in
       Builder.end_block_jump tc_fragment.eval.entry v in
     (*
     let eval_blockt =
       let arg = Builder.begin_block (fresh_label (pair t.t_ann (code_context t1.t_context))) in
       let vstack = Builder.fst arg in
       let vgamma1 = Builder.snd arg in
       let vstacke = Builder.embed vstack t1.t_ann in
       let v = Builder.pair vstacke vgamma1 in
       Builder.end_block_jump t1_fragment.eval.entry v in
     let eval_blockf =
       let arg = Builder.begin_block (fresh_label (pair t.t_ann (code_context t2.t_context))) in
       let vstack = Builder.fst arg in
       let vgamma2 = Builder.snd arg in
       let vstacke = Builder.embed vstack t2.t_ann in
       let v = Builder.pair vstacke vgamma2 in
       Builder.end_block_jump t2_fragment.eval.entry v in
      *)
     let eval_blockc =
       let arg = Builder.begin_block tc_fragment.eval.exit in
       let vstack1, vn = Builder.unpair arg in
       let vp = Builder.project vstack1 (pair t.t_ann
                                            (pair
                                               (code_context t1.t_context)
                                               (code_context t2.t_context)
                                            )) in
       let vstack, vgamma12 = Builder.unpair vp in
       let vgamma1, vgamma2 = Builder.unpair vgamma12 in
       let vz = Builder.primop (Intast.Cinteq) (Builder.pair vn (Builder.intconst 0)) in
       Builder.end_block_case
         vz
         [ (fun _ -> t1_fragment.eval.entry, Builder.pair vstack vgamma1);
           (fun _ -> t2_fragment.eval.entry, Builder.pair vstack vgamma2) ] in
     let eval_blockrt =
       let arg = Builder.begin_block t1_fragment.eval.exit in
       let vstack = Builder.fst arg in
       let vn = Builder.snd arg in
       let v = Builder.pair vstack vn in
       Builder.end_block_jump eval.exit v in
     let eval_blockrf =
       let arg = Builder.begin_block t2_fragment.eval.exit in
       let vstack = Builder.fst arg in
       let vn = Builder.snd arg in
       let v = Builder.pair vstack vn in
       Builder.end_block_jump eval.exit v in
    let access_block =
      let arg = Builder.begin_block access.entry in
      Builder.end_block_jump access.entry arg in
    (* dummy blocks *)
    let access_blockc =
      let arg = Builder.begin_block tc_fragment.access.exit in
      Builder.end_block_jump tc_fragment.access.exit arg in
    let access_block1 =
      let arg = Builder.begin_block t1_fragment.access.exit in
      Builder.end_block_jump t1_fragment.access.exit arg in
    let access_block2 =
      let arg = Builder.begin_block t2_fragment.access.exit in
      Builder.end_block_jump t2_fragment.access.exit arg in
    { eval = eval;
      access = access;
      blocks = [eval_block1; (* eval_blockt; eval_blockf;*) eval_blockc;
                eval_blockrf; eval_blockrt;
                access_block; access_blockc; access_block1; access_block2]
               @ tc_fragment.blocks
               @ t1_fragment.blocks
               @ t2_fragment.blocks;
      context = tc_fragment.context @ t1_fragment.context @ t2_fragment.context
    }

let print_fragment f =
  List.iter f.blocks ~f:(fun block -> Ssa.fprint_block stdout block);
  Printf.printf "\n\n"

let to_ssa t =
  let f = translate t in
  let ret_ty = f.eval.exit.Ssa.message_type in
  let return_block =
    let arg = Builder.begin_block f.eval.exit in
    Builder.end_block_return arg in
  let access_exit_block =
    let arg = Builder.begin_block f.access.exit in
    Builder.end_block_jump f.access.exit arg in
  let blocks = Ident.Table.create () in
  List.iter (return_block :: access_exit_block :: f.blocks)
    ~f:(fun b ->
      let i = (Ssa.label_of_block b).Ssa.name in
      Ident.Table.replace blocks ~key:i ~data:b
    );
  let visited = Ident.Table.create () in
  let rev_sorted_blocks = ref [] in
  let rec sort_blocks i =
    if not (Ident.Table.mem visited i) then
      begin
        Printf.printf "%s\n" (Ident.to_string i);
        Ident.Table.replace visited ~key:i ~data:();

        let b = Ident.Table.find_exn blocks i in
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
