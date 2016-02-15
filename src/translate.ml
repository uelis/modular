open Core_kernel.Std
open Cbvterm

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

let pairB (a1: Basetype.t) (a2: Basetype.t): Basetype.t =
  Basetype.newty (Basetype.PairB(a1, a2))

let sumB = Basetype.sumB

let unPairB a =
  match Basetype.case a with
  | Basetype.Sgn (Basetype.PairB(a1, a2)) -> a1, a2
  | _ -> assert false

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
    pairB (code_context delta) (Cbvtype.code a )

let rec access_entry_type (a: Cbvtype.t): Basetype.t =
  match Cbvtype.case a with
  | Cbvtype.Var -> failwith "var"
  | Cbvtype.Sgn s ->
    match s with
    | Cbvtype.Bool(m) -> pairB m voidB
    | Cbvtype.Nat(m) -> pairB m voidB
    | Cbvtype.Pair(m, (x, y)) ->
      let xentry = access_entry_type x in
      let yentry = access_entry_type y in
      pairB m (sumB [xentry; yentry])
    | Cbvtype.Fun(m, (x, s, c, y)) ->
      let xc = Cbvtype.code x in
      let yentry = access_entry_type y in
      let xexit = access_exit_type x in
      let sum = sumB [pairB s (pairB c xc); yentry; xexit] in
      pairB m sum
and access_exit_type (a: Cbvtype.t): Basetype.t =
  match Cbvtype.case a with
  | Cbvtype.Var -> failwith "var"
  | Cbvtype.Sgn s ->
    match s with
    | Cbvtype.Bool(m) -> pairB m voidB
    | Cbvtype.Nat(m) -> pairB m voidB
    | Cbvtype.Pair(m, (x, y)) ->
      let xexit = access_exit_type x in
      let yexit = access_exit_type y in
      pairB m (sumB [xexit; yexit])
    | Cbvtype.Fun(m, (x, s, _, y)) ->
      let yc = Cbvtype.code y in
      let yexit = access_exit_type y in
      let xentry = access_entry_type x in
      let sumid = Basetype.Data.sumid 3 in
      let params = [pairB s yc; yexit; xentry] in
      let sum = Basetype.newty (Basetype.DataB(sumid, params)) in
      pairB m sum

let fresh_label (name: string) (a : Basetype.t): Ssa.label =
  { Ssa.name = Ident.fresh name;
    Ssa.message_type = a }

let fresh_eval (s: string) (t: Cbvterm.t) : int_interface =
  { entry = fresh_label (s ^ "_eval_entry") (pairB t.t_ann (code_context t.t_context));
    exit  = fresh_label (s ^ "_eval_exit") (pairB t.t_ann (Cbvtype.code t.t_type)) }

let fresh_access (s: string) (a: Cbvtype.t) : int_interface =
  { entry = fresh_label (s ^ "_access_entry") (access_entry_type a);
    exit = fresh_label (s ^ "_access_exit") (access_exit_type a)
  }

let lift_label a l =
  { Ssa.name = l.Ssa.name;
    Ssa.message_type = pairB a (l.Ssa.message_type) }

let lift_int_interface a i = {
  entry = lift_label a i.entry;
  exit = lift_label a i.exit
}

let lift_block (a: Basetype.t) (b: Ssa.block) : Ssa.block =
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
  | Ssa.Unreachable _ -> assert false

let lift (a: Basetype.t) (f: fragment) : fragment =
  { eval = lift_int_interface a f.eval;
    blocks = List.map ~f:(lift_block a) f.blocks;
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
  | (y, _) :: delta ->
    if x = y then
      Builder.snd v
    else
      let v' = Builder.fst v in
      build_context_lookup delta x v'

(* TODO: need to clone values with heap pointers *)
let build_context_map
    (gamma: Cbvtype.t Typing.context)
    (delta: Cbvtype.t Typing.context)
    (code_gamma: Builder.value)
  : Builder.value =
  let rec values gamma code_gamma =
    match gamma with
    | [] -> []
    | (x, _) :: gamma' ->
      let code_gamma', code_x = Builder.unpair code_gamma in
      (x, code_x) :: (values gamma' code_gamma') in
  let gamma_values = values gamma code_gamma in
  let delta_values =
    List.map
      ~f:(fun (x, _) -> (x, List.Assoc.find_exn gamma_values x))
      delta in
  let v = List.fold_right delta_values
      ~init:Builder.unit
      ~f:(fun (_, vx) v -> Builder.pair v vx) in
  v

let print_context c =
  List.iter c
    ~f:(fun (x, a) ->
        Printf.printf "%s:%s, "
          (Ident.to_string x)
          (Printing.string_of_cbvtype ~concise:false a));
  Printf.printf "\n"

let print_fcontext c =
  List.iter c
    ~f:(fun (x, a) ->
        Printf.printf "%s:(%s, %s), "
          (Ident.to_string x)
          (Printing.string_of_basetype a.entry.Ssa.message_type)
          (Printing.string_of_basetype a.exit.Ssa.message_type)
      );
  Printf.printf "\n"

(** Embeds the multiplicities in the context of a fragment as
    specified by the context [outer].

    Inputs are a fagment context [inner] and a typing context [outer]
    that must define the same variables and for each defined variable x,
    the declarations in [outer] and [inner] must have the forms
    [ x: [D]X ] and [ x: (E * (F * X-), E * (F * X+)) ] respectively, where
    [ E*F <= D ].

    The result is an interface where [x] as above gets interface
    [ x: (D * X-, D*  X+) ]. The returned blocks perform embedding and
    projection.
*)
let rec embed_context
    (outer : Cbvtype.t Typing.context)
    (inner : int_interface Typing.context)
  : int_interface Typing.context * Ssa.block list =
  match inner with
  | [] -> [], []
  | (y, y_access) :: inner'  ->
    let outer_gamma', blocks = embed_context outer inner' in
    let y_outer_access = fresh_access "context_embed"
        (List.Assoc.find_exn outer y) in
    let exit_block =
      let arg = Builder.begin_block y_outer_access.exit in
      let vstack_outer, vm = Builder.unpair arg in
      let te, tt = unPairB y_access.exit.Ssa.message_type in
      let tstack_inner, _ = unPairB tt in
      let vstack_pair = Builder.project vstack_outer
          (pairB te tstack_inner) in
      let ve, vstack_inner = Builder.unpair vstack_pair in
      let v = Builder.pair ve (Builder.pair vstack_inner vm) in
      Builder.end_block_jump y_access.exit v in
    let entry_block =
      let arg = Builder.begin_block y_access.entry in
      let ve, vpair = Builder.unpair arg in
      let vstack_inner, vm = Builder.unpair vpair in
      let tstack_outer, _ = unPairB y_outer_access.entry.Ssa.message_type in
      let vstack_outer = Builder.embed (Builder.pair ve vstack_inner) tstack_outer in
      let v = Builder.pair vstack_outer vm in
      Builder.end_block_jump y_outer_access.entry v in
    (y, y_outer_access) :: outer_gamma',
    [entry_block; exit_block] @ blocks

let rec translate (t: Cbvterm.t) : fragment =
  match t.t_desc with
  | Var x ->
    let id = "var" in
    let eval = fresh_eval id t in
    let access = fresh_access id t.t_type in
    let eval_block =
      let arg = Builder.begin_block eval.entry in
      let va, vgamma = Builder.unpair arg in
      let vx = build_context_lookup t.t_context x vgamma in
      let v = Builder.pair va vx in
      Builder.end_block_jump eval.exit v in
    { eval = eval;
      access = access;
      blocks = [eval_block];
      context = [(x, access)]
    }
  | Contr(((x, a), xs), s) ->
    let s_fragment = translate s in
    (*
    print_context s.t_context;
    print_fcontext s_fragment.context;
    *)
    let id = "contr" in
    let eval = {
      entry = fresh_label (id ^ "_eval_entry")
          (pairB t.t_ann (code_context t.t_context));
      exit = s_fragment.eval.exit
    } in
    let x_access = fresh_access "contr" a in
    let tsum =
      let summands = List.map xs
          ~f:(fun x' -> Cbvtype.multiplicity
                 (List.Assoc.find_exn s.t_context x')) in
      let sumid = Basetype.Data.sumid (List.length summands) in
      Basetype.newty (Basetype.DataB(sumid, summands)) in
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
      if xs = [] then
        (* variable unused; dummy block *)
        let arg = Builder.begin_block x_access.exit in
        Builder.end_block_jump x_access.exit arg
      else
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
                   ~f:(fun (x, _) -> not (List.mem xs x)))
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
  | Const(Ast.Cintconst _, _) ->
    assert false
  | Const(Ast.Cintprint, [s]) ->
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
      ignore (Builder.primop (Ssa.Cintprint) vi);
      ignore (Builder.primop (Ssa.Cprint "\n") Builder.unit);
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
  | Const(c, [s1; s2]) ->
    let id, primop = match c with
      | Ast.Cintadd -> "intadd", Ssa.Cintadd
      | Ast.Cintsub -> "intsub", Ssa.Cintsub
      | Ast.Cintmul -> "intmul", Ssa.Cintmul
      | Ast.Cintdiv -> "intdiv", Ssa.Cintdiv
      | Ast.Cinteq -> "inteq", Ssa.Cinteq
      | Ast.Cintlt -> "intlt", Ssa.Cintlt
      | Ast.Cintconst _ -> assert false
      | Ast.Cintprint -> assert false in
    let s1_fragment = translate s1 in
    let s2_fragment = translate s2 in
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
          (pairB t.t_ann (code_context s2.t_context)) in
      let vstack, vgamma2 = Builder.unpair vp in
      let vstack2 = Builder.embed (Builder.pair vstack vn1) s2.t_ann in
      let v = Builder.pair vstack2 vgamma2 in
      Builder.end_block_jump s2_fragment.eval.entry v in
    let eval_block3 =
      let arg = Builder.begin_block s2_fragment.eval.exit in
      let vstack2, vn2 = Builder.unpair arg in
      let vp = Builder.project vstack2 (pairB t.t_ann intB) in
      let vstack, vn1 = Builder.unpair vp in
      let veq = Builder.primop primop (Builder.pair vn1 vn2) in
      let v = Builder.pair vstack veq in
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
  | Const(_, _) ->
    assert false
  | Fun((x, xty), s) ->
    let s_fragment = lift (Cbvtype.multiplicity t.t_type) (translate s) in
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
      let td = Cbvtype.code t.t_type in
      let tcx = Cbvtype.code xty in
      let entry = fresh_label "fun_decode" (pairB te (pairB ta (pairB td tcx))) in
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
      let _(*te*), tf = unPairB access.exit.Ssa.message_type in
      let ve, vy = Builder.unpair arg in
      let vy1 = Builder.inj 1 vy tf in
      let v = Builder.pair ve vy1 in
      Builder.end_block_jump access.exit v in
    let s_x_access_entry_block =
      let arg = Builder.begin_block x_access.entry in
      let _(*te*), tf = unPairB access.exit.Ssa.message_type in
      let ve, vy = Builder.unpair arg in
      let vx2 = Builder.inj 2 vy tf in
      let v = Builder.pair ve vx2 in
      Builder.end_block_jump access.exit v in
    let context, context_blocks =
      let gamma = List.filter s_fragment.context ~f:(fun (y, _) -> x <> y) in
      embed_context t.t_context gamma in
    { eval = eval;
      access = access;
      blocks = [eval_block; access_block; invoke_block;
                s_eval_exit_block; s_access_exit_block; s_x_access_entry_block]
               @ context_blocks
               @ s_fragment.blocks;
      context = context
    }
  | Fix((th, f, x, xty), s) ->
    let s_fragment = lift th (translate s) in
    let id = "fix" in
    let eval = fresh_eval id t in
    let access = fresh_access id t.t_type in
    let x_access = List.Assoc.find_exn s_fragment.context x in
    let f_access = List.Assoc.find_exn s_fragment.context f in
    (* E + H *G *)
    let te = Cbvtype.multiplicity t.t_type in
    let tg = Cbvtype.multiplicity (List.Assoc.find_exn s.t_context f) in
    let thg = pairB th tg in
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
             (pairB th (pairB ta (pairB td tx)))) in
      let vh, vadx = Builder.unpair arg in
      let va, vdx = Builder.unpair vadx in
      let vd, vx = Builder.unpair vdx in
      let vgamma = Builder.project vd (code_context t.t_context) in
      let vgammadx = Builder.pair (Builder.pair vgamma vd) vx in
      let vdelta = build_context_map
          ((x, xty) :: (f, t.t_type) :: t.t_context) s.t_context vgammadx in
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
          (fresh_label (id ^ "invoke_rec") (pairB thg tans)) in
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
    let context, context_blocks =
      let gamma = List.filter s_fragment.context
          ~f:(fun (y, _) -> y <> x && y <> f) in
      embed_context t.t_context gamma in
    { eval = eval;
      access = access;
      blocks = [eval_block; access_block; eval_body_block; invoke_rec_block;
                s_eval_exit_block; s_access_exit_block; x_access_entry_block;
                f_access_entry_block]
               @ context_blocks
               @ s_fragment.blocks;
      context = context
    }
  | Tailfix((th, f, x, xty), s) ->
    let s_fragment = lift th (translate s) in
    let id = "tailfix" in
    let eval = fresh_eval id t in
    let access = fresh_access id t.t_type in
    let x_access = List.Assoc.find_exn s_fragment.context x in
    let f_access = List.Assoc.find_exn s_fragment.context f in
    let te, (_, ta, td, _) = Cbvtype.unFun t.t_type in
    let tea = pairB te ta in
    let dummy_block =
      let l = fresh_label (id ^ "dummy") unitB in
      let arg = Builder.begin_block l in
      Builder.end_block_jump l arg in
    let eval_block =
      let arg = Builder.begin_block eval.entry in
      let vstack, vgamma = Builder.unpair arg in
      let vclosure = Builder.embed vgamma (Cbvtype.code t.t_type) in
      let v = Builder.pair vstack vclosure in
      Builder.end_block_jump eval.exit v in
    let eval_body_block =
      let tx = Cbvtype.code xty in
      let arg = Builder.begin_block
          (fresh_label (id ^ "eval_body")
             (pairB te (pairB ta (pairB td tx)))) in
      let ve, vadx = Builder.unpair arg in
      let va, vdx = Builder.unpair vadx in
      let vd, vx = Builder.unpair vdx in
      let vgamma = Builder.project vd (code_context t.t_context) in
      let vgammadx = Builder.pair (Builder.pair vgamma vd) vx in
      let vdelta = build_context_map
          ((x, xty) :: (f, t.t_type) :: t.t_context) s.t_context vgammadx in
      let vh = Builder.embed (Builder.pair ve va) th in
      let vu = Builder.embed Builder.unit s.t_ann in
      let v = Builder.pair vh (Builder.pair vu vdelta) in
      Builder.end_block_jump s_fragment.eval.entry v in
    let access_block =
      let arg = Builder.begin_block access.entry in
      let ve, vreq = Builder.unpair arg in
      Builder.end_block_case
        vreq
        [ (fun c -> Ssa.label_of_block eval_body_block, Builder.pair ve c);
          (fun c -> Ssa.label_of_block dummy_block, Builder.unit);
          (fun c -> Ssa.label_of_block dummy_block, Builder.unit) ] in
    let s_eval_exit_block =
      let arg = Builder.begin_block s_fragment.eval.exit in
      let vh, vum = Builder.unpair arg in
      let vm = Builder.snd vum in
      let vea = Builder.project vh tea in
      let ve = Builder.fst vea in
      let va = Builder.snd vea in
      let _, tans = unPairB access.exit.Ssa.message_type in
      let vm0 = Builder.inj 0 (Builder.pair va vm) tans in
      Builder.end_block_jump access.exit (Builder.pair ve vm0) in
    let s_access_exit_block =
      let _ = Builder.begin_block s_fragment.access.exit in
      Builder.end_block_jump (Ssa.label_of_block dummy_block) Builder.unit in
    let x_access_entry_block =
      let _ = Builder.begin_block x_access.entry in
      Builder.end_block_jump (Ssa.label_of_block dummy_block) Builder.unit in
    let f_access_entry_block =
      let arg = Builder.begin_block f_access.entry in
      let vh, vgm = Builder.unpair arg in
      let vea = Builder.project vh tea in
      let ve = Builder.fst vea in
      let va = Builder.snd vea in
      let _, vm = Builder.unpair vgm in
      Builder.end_block_case
        vm
        [ (fun c -> Ssa.label_of_block eval_body_block,
                    Builder.pair ve (Builder.pair va (Builder.snd c)));
          (fun c -> Ssa.label_of_block dummy_block, Builder.unit);
          (fun c -> Ssa.label_of_block dummy_block, Builder.unit) ] in
    let context, context_blocks =
      let gamma = List.filter s_fragment.context
          ~f:(fun (y, _) -> y <> x && y <> f) in
      embed_context t.t_context gamma in
    { eval = eval;
      access = access;
      blocks = [eval_block; access_block; eval_body_block;
                s_eval_exit_block; s_access_exit_block; x_access_entry_block;
                f_access_entry_block; dummy_block]
               @ context_blocks
               @ s_fragment.blocks;
      context = context
    }
  | Pair(t1, t2) ->
    let t1_fragment = translate t1 in
    let t2_fragment = translate t2 in
    let id = "pair" in
    let eval = fresh_eval id t in
    let access = fresh_access id t.t_type in
    (* evaluation blocks *)
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
          (pairB t.t_ann (code_context t2.t_context)) in
      let vu, vdelta = Builder.unpair vu_delta in
      let vu_f = Builder.pair vu vf in
      let ve' = Builder.embed vu_f t2.t_ann in
      let v = Builder.pair ve' vdelta in
      Builder.end_block_jump t2_fragment.eval.entry v in
    let block3 =
      let arg = Builder.begin_block t2_fragment.eval.exit in
      let ve, v2 = Builder.unpair arg in
      let vu_f = Builder.project ve (pairB t.t_ann (Cbvtype.code t1.t_type)) in
      let vu, v1 = Builder.unpair vu_f in
      let v = Builder.pair vu (Builder.pair v1 v2) in
      Builder.end_block_jump eval.exit v in
    let outer_multiplicity, inner_access_entry = unPairB access.entry.Ssa.message_type in
    let left_inner_access_entry, right_inner_access_entry =
        match Basetype.case inner_access_entry with
        | Basetype.Var -> assert false
        | Basetype.Sgn s ->
          match s with
          | Basetype.DataB(_, [l; r]) -> l, r
          | _ -> assert false in
    let access_entry1 =
      let tm, tq = unPairB left_inner_access_entry in
      let arg = Builder.begin_block
          (fresh_label "pair_access1"
             (pairB outer_multiplicity (pairB tm tq))) in
      let v_mult = Builder.fst arg in
      let vq = Builder.snd arg in
      let v_inner_mult = Builder.fst vq in
      let v_inner_q = Builder.snd vq in
      let t1_multiplicty, _ = unPairB t1_fragment.access.entry.Ssa.message_type in
      let vm = Builder.embed (Builder.pair v_mult v_inner_mult) t1_multiplicty in
      let v = Builder.pair vm v_inner_q in
      Builder.end_block_jump t1_fragment.access.entry v in
    let access_entry2 =
      let tm, tq = unPairB right_inner_access_entry in
      let arg = Builder.begin_block
          (fresh_label "pair_access2"
             (pairB outer_multiplicity (pairB tm tq))) in
      let v_mult = Builder.fst arg in
      let vq = Builder.snd arg in
      let v_inner_mult = Builder.fst vq in
      let v_inner_q = Builder.snd vq in
      let t2_multiplicty, _ = unPairB t2_fragment.access.entry.Ssa.message_type in
      let vm = Builder.embed (Builder.pair v_mult v_inner_mult) t2_multiplicty in
      let v = Builder.pair vm v_inner_q in
      Builder.end_block_jump t2_fragment.access.entry v in
    let access_pair =
      let arg = Builder.begin_block access.entry in
      let vm = Builder.fst arg in
      let vq = Builder.snd arg in
      Builder.end_block_case
        vq
        [ (fun c -> Ssa.label_of_block access_entry1, Builder.pair vm c);
          (fun c -> Ssa.label_of_block access_entry2, Builder.pair vm c) ] in
    let _, inner_access_exit = unPairB access.exit.Ssa.message_type in
    let access_exit1 =
      let arg = Builder.begin_block t1_fragment.access.exit in
      let tm, _ = unPairB left_inner_access_entry in
      let vm1 = Builder.fst arg in
      let va = Builder.snd arg in
      let vm = Builder.project vm1 (pairB outer_multiplicity tm) in
      let vmo = Builder.fst vm in
      let vmi = Builder.snd vm in
      let vi = Builder.inj 0 (Builder.pair vmi va) inner_access_exit in
      let v = Builder.pair vmo vi in
      Builder.end_block_jump access.exit v in
    let access_exit2 =
      let arg = Builder.begin_block t2_fragment.access.exit in
      let tm, _ = unPairB right_inner_access_entry in
      let vm1 = Builder.fst arg in
      let va = Builder.snd arg in
      let vm = Builder.project vm1 (pairB outer_multiplicity tm) in
      let vmo = Builder.fst vm in
      let vmi = Builder.snd vm in
      let vi = Builder.inj 1 (Builder.pair vmi va) inner_access_exit in
      let v = Builder.pair vmo vi in
      Builder.end_block_jump access.exit v in
    { eval = eval;
      access = access;
      blocks = [block1; block2; block3; access_entry1; access_entry2; access_pair
               ; access_exit1; access_exit2]
               @ t1_fragment.blocks
               @ t2_fragment.blocks;
      context = t1_fragment.context @ t2_fragment.context
    }
  | Fst(t1) ->
    let t1_fragment = translate t1 in
    let id = "fst" in
    let eval = fresh_eval id t in
    let access = fresh_access id t.t_type in
    (* evaluation blocks *)
    let block1 =
      let arg = Builder.begin_block eval.entry in
      Builder.end_block_jump t1_fragment.eval.entry arg in
    let block2 =
      let arg = Builder.begin_block t1_fragment.eval.exit in
      let vm, vp = Builder.unpair arg in
      let vp1 = Builder.fst vp in
      let v = Builder.pair vm vp1 in
      Builder.end_block_jump eval.exit v in
    let access_entry =
      let arg = Builder.begin_block access.entry in
      let vu = Builder.unit in
      let tm, tq = unPairB t1_fragment.access.entry.Ssa.message_type in
      let vm = Builder.embed vu tm in
      let vq = Builder.inj 0 arg tq in
      let v = Builder.pair vm vq in
      Builder.end_block_jump t1_fragment.access.entry v in
    let assert_false =
      let l = fresh_label "assert_false" unitB in
      let arg = Builder.begin_block l in
      Builder.end_block_jump l arg in
    let access_exit =
      let arg = Builder.begin_block t1_fragment.access.exit in
      let va = Builder.snd arg in
      Builder.end_block_case
        va
        [ (fun c -> access.exit, c);
          (fun _ -> Ssa.label_of_block assert_false, Builder.unit) ] in
    { eval = eval;
      access = access;
      blocks = [block1; block2; access_entry; access_exit; assert_false]
               @ t1_fragment.blocks;
      context = t1_fragment.context
    }
  | Snd(t1) ->
    let t1_fragment = translate t1 in
    let id = "snd" in
    let eval = fresh_eval id t in
    let access = fresh_access id t.t_type in
    (* evaluation blocks *)
    let block1 =
      let arg = Builder.begin_block eval.entry in
      Builder.end_block_jump t1_fragment.eval.entry arg in
    let block2 =
      let arg = Builder.begin_block t1_fragment.eval.exit in
      let vm, vp = Builder.unpair arg in
      let vp2 = Builder.snd vp in
      let v = Builder.pair vm vp2 in
      Builder.end_block_jump eval.exit v in
    let access_entry =
      let arg = Builder.begin_block access.entry in
      let vu = Builder.unit in
      let tm, tq = unPairB t1_fragment.access.entry.Ssa.message_type in
      let vm = Builder.embed vu tm in
      let vq = Builder.inj 1 arg tq in
      let v = Builder.pair vm vq in
      Builder.end_block_jump t1_fragment.access.entry v in
    let assert_false =
      let l = fresh_label "assert_false" unitB in
      let arg = Builder.begin_block l in
      Builder.end_block_jump l arg in
    let access_exit =
      let arg = Builder.begin_block t1_fragment.access.exit in
      let va = Builder.snd arg in
      Builder.end_block_case
        va
        [ (fun _ -> Ssa.label_of_block assert_false, Builder.unit) ;
          (fun c -> access.exit, c) ] in
    { eval = eval;
      access = access;
      blocks = [block1; block2; access_entry; access_exit; assert_false]
               @ t1_fragment.blocks;
      context = t1_fragment.context
    }
  | App(t1, t2) ->
    let t1_fragment = translate t1 in
    let t2_fragment = translate t2 in
    let id = "app" in
    let eval = fresh_eval id t in
    let access = fresh_access id t.t_type in
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
          (pairB t.t_ann (code_context t2.t_context)) in
      let vu, vdelta = Builder.unpair vu_delta in
      let vu_f = Builder.pair vu vf in
      let ve' = Builder.embed vu_f t2.t_ann in
      let v = Builder.pair ve' vdelta in
      Builder.end_block_jump t2_fragment.eval.entry v in
    let block3 =
      let arg = Builder.begin_block t2_fragment.eval.exit in
      let ve, vx = Builder.unpair arg in
      let vu_f = Builder.project ve (pairB t.t_ann (Cbvtype.code t1.t_type)) in
      let vu, vf = Builder.unpair vu_f in
      let _, (_, tv, _, _) = Cbvtype.unFun t1.t_type in
      let vv = Builder.embed vu tv in
      let vvfx = Builder.pair vv (Builder.pair vf vx) in
      let td, tfunacc = unPairB t1_fragment.access.entry.Ssa.message_type in
      let vfunacc = Builder.inj 0 vvfx tfunacc in
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
    let block8 =
      let _, (_, tv, _, _) = Cbvtype.unFun t1.t_type in
      let _, tres = unPairB eval.exit.Ssa.message_type in
      let arg = Builder.begin_block (fresh_label "decode_stack" (pairB tv tres)) in
      let vv, vres = Builder.unpair arg in
      let vu = Builder.project vv t.t_ann in
      let v = Builder.pair vu vres in
      Builder.end_block_jump eval.exit v in
    let case_block =
      let arg = Builder.begin_block t1_fragment.access.exit in
      let vfun = Builder.snd arg in
      Builder.end_block_case
        vfun
        [ (fun c -> Ssa.label_of_block block8, c);
          (fun c -> access.exit, c);
          (fun c -> t2_fragment.access.entry, c) ] in
    { eval = eval;
      access = access;
      blocks = [block1; block2; block3; block5; block7; block8; case_block]
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
    (* TODO: extremely ugly!! *)
    let inject_code k v a1 a2 a =
      let i = match k with
        | `Case1 -> 0
        | `Case2 -> 1 in
      match Cbvtype.case a with
      | Cbvtype.Sgn (Cbvtype.Nat _) -> v
      | Cbvtype.Sgn (Cbvtype.Fun _) ->
        let d1 = Cbvtype.code a1 in
        let d2 = Cbvtype.code a2 in
        let d = Cbvtype.code a in
        let vi = Builder.inj i v (Basetype.sumB [d1; d2]) in
        Builder.embed vi d
      (* TODO: pair types are missing *)
      | _ -> assert false in
    let rec join (access1, a1) (access2, a2) a : int_interface * (Ssa.block list) =
        match Cbvtype.case a1, Cbvtype.case a2, Cbvtype.case a with
          | Cbvtype.Sgn (Cbvtype.Nat _),
            Cbvtype.Sgn (Cbvtype.Nat _),
            Cbvtype.Sgn (Cbvtype.Nat _) ->
            let access = fresh_access "joinNat" a in
            let block1 =
              let arg = Builder.begin_block access.entry in
              Builder.end_block_jump access.entry arg in
            let block2 =
              let arg = Builder.begin_block access1.exit in
              Builder.end_block_jump access1.exit arg in
            let block3 =
              let arg = Builder.begin_block access2.exit in
              Builder.end_block_jump access2.exit arg in
            access, [block1; block2; block3]
          | Cbvtype.Sgn (Cbvtype.Fun (m1, (x1, c1, d1, y1))),
            Cbvtype.Sgn (Cbvtype.Fun (m2, (x2, c2, d2, y2))),
            Cbvtype.Sgn (Cbvtype.Fun (m , (x , c , d , y ))) ->
            assert (Basetype.equals m m1);
            assert (Basetype.equals m m2);
            assert (Basetype.equals c c1);
            assert (Basetype.equals c c2);
            let b = Cbvtype.multiplicity x in
            let b1 = Cbvtype.multiplicity x1 in
            let b2 = Cbvtype.multiplicity x2 in
            let b12 = Basetype.newty
                (Basetype.DataB(Basetype.Data.sumid 2, [b1; b2])) in
            let d12 = Basetype.newty
                (Basetype.DataB(Basetype.Data.sumid 2, [d1; d2])) in
            let access = fresh_access "joinFun" a in
            (* TODO: Move outside? *)
            let inject kind vm i v =
              let label = match kind with
                | `Entry1 -> access1.entry
                | `Entry2 -> access2.entry
                | `Exit -> access.exit in
              let _, t = unPairB label.Ssa.message_type in
              let j = match i with
                | `Eval -> 0
                | `Res -> 1
                | `Arg -> 2 in
              Builder.pair vm (Builder.inj j v t) in
            (* Entry block *)
            let fun_eval_entry_block =
              let arg = Builder.begin_block
                  (fresh_label "join1" (pairB m (pairB c (pairB d (Cbvtype.code x))))) in
              let vm, vcdx = Builder.unpair arg in
              let vc, vdx = Builder.unpair vcdx in
              let vd, vx = Builder.unpair vdx in
              let vd12 = Builder.project vd d12 in
              Builder.end_block_case vd12
                [ (fun vd1 ->
                      let vp = Builder.pair vc (Builder.pair vd1 vx) in
                      let v = inject `Entry1 vm `Eval vp in
                      access1.entry, v);
                  (fun vd2 ->
                     let vp = Builder.pair vc (Builder.pair vd2 vx) in
                     let v = inject `Entry2 vm `Eval vp in
                     access2.entry, v)
                ] in
            (* Recursively join y1 and y2 to y and lift with m. *)
            let lift_y1_access, lift_y2_access, lift_y_access, join_y_blocks =
              let a1 = fresh_access "fun1_res" y1 in
              let a2 = fresh_access "fun2_res" y2 in
              let a, bs = join (a1, y1) (a2, y2) y in
              lift_int_interface m a1,
              lift_int_interface m a2,
              lift_int_interface m a,
              List.map bs ~f:(lift_block m) in
            let fun1_res_block =
              let arg = Builder.begin_block lift_y1_access.entry in
              let vm, _(*vy*) = Builder.unpair arg in
              let v = inject `Entry1 vm `Res arg in
              Builder.end_block_jump access1.entry v in
            let fun2_res_block =
              let arg = Builder.begin_block lift_y2_access.entry in
              let vm, _(*vy*) = Builder.unpair arg in
              let v = inject `Entry2 vm `Res arg in
              Builder.end_block_jump access2.entry v in
            let fun_res_block =
              let arg = Builder.begin_block lift_y_access.exit in
              let vm, vy = Builder.unpair arg in
              let v = inject `Exit vm `Res vy in
              Builder.end_block_jump access.exit v in
            let fun_arg_exit_block =
              let arg = Builder.begin_block
                  (fresh_label "join_arg_exit" (pairB m (access_exit_type x))) in
              let vm, vv = Builder.unpair arg in
              let vb, vx = Builder.unpair vv in
              let vb12 = Builder.project vb b12 in
              Builder.end_block_case vb12
                [ (fun vb1 ->
                      let vp = Builder.pair vb1 vx in
                      let v = inject `Entry1 vm `Arg vp in
                      access1.entry, v);
                  (fun vb2 ->
                     let vp = Builder.pair vb2 vx in
                     let v = inject `Entry2  vm `Arg vp in
                     access2.entry, v)
                ] in
            let entry_block =
              let arg = Builder.begin_block access.entry in
              let vm, vv = Builder.unpair arg in
              Builder.end_block_case vv
                [ (fun c -> Ssa.label_of_block fun_eval_entry_block, Builder.pair vm c);
                  (fun c -> lift_y_access.entry, Builder.pair vm c);
                  (fun c -> Ssa.label_of_block fun_arg_exit_block, Builder.pair vm c)
                ] in
            (* Exit blocks *)
            let fun_arg_entry_block =
              let _, vx = unPairB (access_entry_type x) in
              let arg = Builder.begin_block
                  (fresh_label "fun_arg_entry" (pairB m (pairB b12 vx))) in
              let vm, vb12x = Builder.unpair arg in
              let vb12, vx = Builder.unpair vb12x in
              let vb = Builder.embed vb12 b in
              let vbx = Builder.pair vb vx in
              let v = inject `Exit vm `Arg vbx in
              Builder.end_block_jump access.exit v in
            let exit_block1 =
              let arg = Builder.begin_block access1.exit in
              let vm, vv = Builder.unpair arg in
              Builder.end_block_case vv
                [ (fun vres ->
                      let vc, vd1 = Builder.unpair vres in
                      let vy = inject_code `Case1 vd1 y1 y2 y in
                      let v = inject `Exit vm `Eval (Builder.pair vc vy) in
                      access.exit, v);
                  (fun vy1 ->
                     lift_y1_access.exit, Builder.pair vm vy1);
                  (fun varg ->
                     let vb1, vx = Builder.unpair varg in
                     let vb12 = Builder.inj 0 vb1 b12 in
                     let vb12x = Builder.pair vb12 vx in
                     let v = Builder.pair vm vb12x in
                     Ssa.label_of_block fun_arg_entry_block, v)
                ] in
            let exit_block2 =
              let arg = Builder.begin_block access2.exit in
              let vm, vv = Builder.unpair arg in
              Builder.end_block_case vv
                [ (fun vres ->
                      let vc, vd2 = Builder.unpair vres in
                      let vy = inject_code `Case2 vd2 y1 y2 y in
                      let v = inject `Exit vm `Eval (Builder.pair vc vy) in
                      access.exit, v);
                  (fun vy2 ->
                     lift_y2_access.exit, Builder.pair vm vy2);
                  (fun varg ->
                     let vb2, vx = Builder.unpair varg in
                     let vb12 = Builder.inj 1 vb2 b12 in
                     let vb12x = Builder.pair vb12 vx in
                     let v = Builder.pair vm vb12x in
                     Ssa.label_of_block fun_arg_entry_block, v)
                ] in
            access,
            [fun_eval_entry_block; fun1_res_block; fun2_res_block; fun_res_block;
             fun_arg_entry_block; fun_arg_exit_block;
             entry_block; exit_block1; exit_block2]
            @ join_y_blocks
          | _ -> assert false in
    let eval_block1 =
      let arg = Builder.begin_block eval.entry in
      let vstack, vgamma = Builder.unpair arg in
      let vgammac = build_context_map t.t_context tc.t_context vgamma in
      let vgamma1 = build_context_map t.t_context t1.t_context vgamma in
      let vgamma2 = build_context_map t.t_context t2.t_context vgamma in
      let vstack1 = Builder.embed (Builder.pair vstack (Builder.pair vgamma1 vgamma2)) tc.t_ann in
      let v = Builder.pair vstack1 vgammac in
      Builder.end_block_jump tc_fragment.eval.entry v in
    let eval_blockc =
      let arg = Builder.begin_block tc_fragment.eval.exit in
      let vstack1, vz = Builder.unpair arg in
      let vp = Builder.project vstack1 (pairB t.t_ann
                                          (pairB
                                             (code_context t1.t_context)
                                             (code_context t2.t_context)
                                          )) in
      let vstack, vgamma12 = Builder.unpair vp in
      let vgamma1, vgamma2 = Builder.unpair vgamma12 in
      Builder.end_block_case
        vz
        [ (fun _ -> t1_fragment.eval.entry, Builder.pair vstack vgamma1);
          (fun _ -> t2_fragment.eval.entry, Builder.pair vstack vgamma2) ] in
    let eval_blockrt =
      let arg = Builder.begin_block t1_fragment.eval.exit in
      let vstack = Builder.fst arg in
      let vn = Builder.snd arg in
      let v = Builder.pair vstack (inject_code `Case1 vn t1.t_type t2.t_type t.t_type) in
      Builder.end_block_jump eval.exit v in
    let eval_blockrf =
      let arg = Builder.begin_block t2_fragment.eval.exit in
      let vstack = Builder.fst arg in
      let vn = Builder.snd arg in
      let v = Builder.pair vstack (inject_code `Case2 vn t1.t_type t2.t_type t.t_type) in
      Builder.end_block_jump eval.exit v in
    let access_blockc =
      let arg = Builder.begin_block tc_fragment.access.exit in
      Builder.end_block_jump tc_fragment.access.exit arg in
    let access, join_blocks =
      join
        (t1_fragment.access, t1.t_type)
        (t2_fragment.access, t2.t_type)
        t.t_type in
    { eval = eval;
      access = access;
      blocks = [eval_block1; eval_blockc;
                eval_blockrf; eval_blockrt; access_blockc]
               @ join_blocks
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
        Ident.Table.set blocks ~key:i ~data:b
      );
  let visited = Ident.Table.create () in
  let rev_sorted_blocks = ref [] in
  let rec sort_blocks i =
    if not (Ident.Table.mem visited i) then
      begin
        (* Printf.printf "%s\n" (Ident.to_string i); *)
        Ident.Table.set visited ~key:i ~data:();

        let b = Ident.Table.find_exn blocks i in
        rev_sorted_blocks := b :: !rev_sorted_blocks;
        List.iter (Ssa.targets_of_block b)
          ~f:(fun l -> sort_blocks l.Ssa.name)
      end in
  sort_blocks f.eval.entry.Ssa.name;
  Ssa.make
    ~func_name:"main"
    ~entry_label:f.eval.entry
    ~blocks: (List.rev !rev_sorted_blocks)
    ~return_type: ret_ty
