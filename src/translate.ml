(* TODO: reverse block arguments? *)
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

let unPairB_singleton x =
  let a = List.last_exn x in
  unPairB a

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

let stage = ref []
let enter_stage a =
  stage := a :: !stage
let leave_stage () =
  stage := List.tl_exn !stage

let fresh_label (name: string) (a : Basetype.t list): Ssa.label =
  { Ssa.name = Ident.fresh name;
    Ssa.arg_types = (List.rev !stage) @ a }

let fresh_eval (s: string) (t: Cbvterm.t) : int_interface =
  { entry = fresh_label (s ^ "_eval_entry") [pairB t.t_ann (code_context t.t_context)];
    exit  = fresh_label (s ^ "_eval_exit") [pairB t.t_ann (Cbvtype.code t.t_type)] }

let fresh_access (s: string) (a: Cbvtype.t) : int_interface =
  { entry = fresh_label (s ^ "_access_entry") [access_entry_type a];
    exit = fresh_label (s ^ "_access_exit") [access_exit_type a]
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

    TODO: specify interfaces
*)
let rec embed_context
    (outer : Cbvtype.t Typing.context)
    (inner : int_interface Typing.context)
  : int_interface Typing.context =
  match inner with
  | [] -> []
  | (y, y_access) :: inner'  ->
    let outer_gamma' = embed_context outer inner' in
    let y_outer_access = fresh_access "context_embed"
        (List.Assoc.find_exn outer y) in
    (* exit *)
    let arg = Builder.begin_block y_outer_access.exit in
    let vstack_outer, vm = Builder.unpair arg in
    let te, tt =
      match List.rev y_access.exit.Ssa.arg_types with
      | tt :: te :: _ -> te, tt
      | _ -> assert false in
    let tstack_inner, _ = unPairB tt in
    let vstack_pair = Builder.project vstack_outer
        (pairB te tstack_inner) in
    let ve, vstack_inner = Builder.unpair vstack_pair in
    let v = Builder.pair vstack_inner vm in
    Builder.end_block_jump y_access.exit [ve; v];
    (* entry *)
    let ve, vpair = Builder.begin_block2 y_access.entry in
    let vstack_inner, vm = Builder.unpair vpair in
    let tstack_outer, _ = unPairB_singleton y_outer_access.entry.Ssa.arg_types in
    let vstack_outer = Builder.embed (Builder.pair ve vstack_inner) tstack_outer in
    let v = Builder.pair vstack_outer vm in
    Builder.end_block_jump y_outer_access.entry [v];
    (y, y_outer_access) :: outer_gamma'

(* TODO: extremely ugly!! *)
let rec join_code k v a1 a2 a =
  let i = match k with
    | `Left -> 0
    | `Right -> 1 in
  match Cbvtype.case a with
  | Cbvtype.Sgn (Cbvtype.Bool _) -> v
  | Cbvtype.Sgn (Cbvtype.Nat _) -> v
  | Cbvtype.Sgn (Cbvtype.Pair (_, (x, y))) ->
    let _, (x1, y1) = Cbvtype.unPair a1 in
    let _, (x2, y2) = Cbvtype.unPair a2 in
    let vx, vy = Builder.unpair v in
    let vx' = join_code k vx x1 x2 x in
    let vy' = join_code k vy y1 y2 y in
    Builder.pair vx' vy'
  | Cbvtype.Sgn (Cbvtype.Fun _) ->
    let d1 = Cbvtype.code a1 in
    let d2 = Cbvtype.code a2 in
    let d = Cbvtype.code a in
    let vi = Builder.inj i v (Basetype.sumB [d1; d2]) in
    Builder.embed vi d
  | Cbvtype.Var ->
    assert false

let rec join (access1, a1) (access2, a2) a : int_interface =
  match Cbvtype.case a1, Cbvtype.case a2, Cbvtype.case a with
  | Cbvtype.Sgn (Cbvtype.Bool _),
    Cbvtype.Sgn (Cbvtype.Bool _),
    Cbvtype.Sgn (Cbvtype.Bool _)
  | Cbvtype.Sgn (Cbvtype.Nat _),
    Cbvtype.Sgn (Cbvtype.Nat _),
    Cbvtype.Sgn (Cbvtype.Nat _) ->
    let access = fresh_access "joinBase" a in
    (* Block 1 *)
    let arg = Builder.begin_block access.entry in
    Builder.end_block_jump access.entry [arg];
    (* Block 2 *)
    let arg = Builder.begin_block access1.exit in
    Builder.end_block_jump access1.exit [arg];
    (* Block 3 *)
    let arg = Builder.begin_block access2.exit in
    Builder.end_block_jump access2.exit [arg];
    access
  | Cbvtype.Sgn (Cbvtype.Pair (m1, (x1, y1))),
    Cbvtype.Sgn (Cbvtype.Pair (m2, (x2, y2))),
    Cbvtype.Sgn (Cbvtype.Pair (m , (x , y ))) ->
    assert (Basetype.equals m m1);
    assert (Basetype.equals m m2);
    let access = fresh_access "joinPair" a in
    (* Entry block *)
    let lift_x1_access, lift_x2_access, lift_x_access =
      enter_stage m;
      let a1 = fresh_access "pairx1" x1 in
      let a2 = fresh_access "pairx2" x2 in
      let a = join (a1, x1) (a2, x2) x in
      leave_stage ();
      a1, a2, a in
    let lift_y1_access, lift_y2_access, lift_y_access =
      enter_stage m;
      let a1 = fresh_access "pairy1" y1 in
      let a2 = fresh_access "pairy2" y2 in
      let a = join (a1, y1) (a2, y2) y in
      leave_stage ();
      a1, a2, a in
    let inject kind vm i v =
      let label = match kind with
        | `Entry1 -> access1.entry
        | `Entry2 -> access2.entry
        | `Exit -> access.exit in
      let j = match i with
        | `X -> 0
        | `Y -> 1 in
      let _, t = unPairB_singleton label.Ssa.arg_types in
      Builder.pair vm (Builder.inj j v t) in
    (* x1 entry *)
    let vm, vx = Builder.begin_block2 lift_x1_access.entry in
    let v = inject `Entry1 vm `X vx in
    Builder.end_block_jump access1.entry [v];
    (* y1 entry *)
    let vm, vy = Builder.begin_block2 lift_y1_access.entry in
    let v = inject `Entry1 vm `Y vy in
    Builder.end_block_jump access1.entry [v];
    (* x2 entry *)
    let vm, vx = Builder.begin_block2 lift_x2_access.entry in
    let v = inject `Entry2 vm `X vx in
    Builder.end_block_jump access2.entry [v];
    (* y2 entry *)
    let vm, vy = Builder.begin_block2 lift_y2_access.entry in
    let v = inject `Entry2 vm `Y vy in
    Builder.end_block_jump access2.entry [v];
    (* entry *)
    let arg = Builder.begin_block access.entry in
    let vm, vxy = Builder.unpair arg in
    Builder.end_block_case vxy
      [(fun c -> lift_x_access.entry, [vm; c]);
       (fun c -> lift_y_access.entry, [vm; c])
      ];
    (* exit 1 *)
    let arg = Builder.begin_block access1.exit in
    let vm, vxy = Builder.unpair arg in
    Builder.end_block_case vxy
      [(fun c -> lift_x1_access.exit, [vm; c]);
       (fun c -> lift_y1_access.exit, [vm; c])
      ];
    (* exit 2 *)
    let arg = Builder.begin_block access2.exit in
    let vm, vxy = Builder.unpair arg in
    Builder.end_block_case vxy
      [(fun c -> lift_x2_access.exit, [vm; c]);
       (fun c -> lift_y2_access.exit, [vm; c])
      ];
    (* result x *)
    let vm, vx = Builder.begin_block2 lift_x_access.exit in
    let v = inject `Exit vm `X vx in
    Builder.end_block_jump access.exit [v];
    (* result y *)
    let vm, vy = Builder.begin_block2 lift_y_access.exit in
    let v = inject `Exit vm `Y vy in
    Builder.end_block_jump access.exit [v];
    access
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
      let _, t = unPairB_singleton label.Ssa.arg_types in
      let j = match i with
        | `Eval -> 0
        | `Res -> 1
        | `Arg -> 2 in
      Builder.pair vm (Builder.inj j v t) in
    (* Entry block *)
    let fun_eval_entry_block =
      fresh_label "join1" [pairB m (pairB c (pairB d (Cbvtype.code x)))] in
    let _ =
      let arg = Builder.begin_block fun_eval_entry_block in
      let vm, vcdx = Builder.unpair arg in
      let vc, vdx = Builder.unpair vcdx in
      let vd, vx = Builder.unpair vdx in
      let vd12 = Builder.project vd d12 in
      Builder.end_block_case vd12
        [ (fun vd1 ->
              let vp = Builder.pair vc (Builder.pair vd1 vx) in
              let v = inject `Entry1 vm `Eval vp in
              access1.entry, [v]);
          (fun vd2 ->
             let vp = Builder.pair vc (Builder.pair vd2 vx) in
             let v = inject `Entry2 vm `Eval vp in
             access2.entry, [v])
        ] in
    (* Recursively join y1 and y2 to y and lift with m. *)
    let lift_y1_access, lift_y2_access, lift_y_access =
      enter_stage m;
      let a1 = fresh_access "fun1_res" y1 in
      let a2 = fresh_access "fun2_res" y2 in
      let a = join (a1, y1) (a2, y2) y in
      leave_stage ();
      a1, a2, a in
    (* fun 1 res *)
    let vm, vy = Builder.begin_block2 lift_y1_access.entry in
    let v = inject `Entry1 vm `Res (Builder.pair vm vy) in
    Builder.end_block_jump access1.entry [v];
    (* fun 2 res *)
    let vm, vy = Builder.begin_block2 lift_y2_access.entry in
    let v = inject `Entry2 vm `Res (Builder.pair vm vy) in
    Builder.end_block_jump access2.entry [v];
    (* fun res *)
    let vm, vy = Builder.begin_block2 lift_y_access.exit in
    let v = inject `Exit vm `Res vy in
    Builder.end_block_jump access.exit [v];
    (* fun arg exit *)
    let fun_arg_exit_block =
      fresh_label "join_arg_exit" [pairB m (access_exit_type x)] in
    let arg = Builder.begin_block fun_arg_exit_block in
    let vm, vv = Builder.unpair arg in
    let vb, vx = Builder.unpair vv in
    let vb12 = Builder.project vb b12 in
    Builder.end_block_case vb12
      [ (fun vb1 ->
            let vp = Builder.pair vb1 vx in
            let v = inject `Entry1 vm `Arg vp in
            access1.entry, [v]);
        (fun vb2 ->
           let vp = Builder.pair vb2 vx in
           let v = inject `Entry2  vm `Arg vp in
           access2.entry, [v])
      ];
    (* entry *)
    let arg = Builder.begin_block access.entry in
    let vm, vv = Builder.unpair arg in
    Builder.end_block_case vv
      [ (fun c -> fun_eval_entry_block, [Builder.pair vm c]);
        (fun c -> lift_y_access.entry, [vm; c]);
        (fun c -> fun_arg_exit_block, [Builder.pair vm c])
      ];
    (* fun arg entry *)
    let fun_arg_entry_block =
      let _, vx = unPairB (access_entry_type x) in
      fresh_label "fun_arg_entry" [pairB m (pairB b12 vx)]in
    let arg = Builder.begin_block fun_arg_entry_block in
    let vm, vb12x = Builder.unpair arg in
    let vb12, vx = Builder.unpair vb12x in
    let vb = Builder.embed vb12 b in
    let vbx = Builder.pair vb vx in
    let v = inject `Exit vm `Arg vbx in
    Builder.end_block_jump access.exit [v];
    (* exit 1 *)
    let arg = Builder.begin_block access1.exit in
    let vm, vv = Builder.unpair arg in
    Builder.end_block_case vv
      [ (fun vres ->
            let vc, vd1 = Builder.unpair vres in
            let vy = join_code `Left vd1 y1 y2 y in
            let v = inject `Exit vm `Eval (Builder.pair vc vy) in
            access.exit, [v]);
        (fun vy1 ->
           lift_y1_access.exit, [vm; vy1]);
        (fun varg ->
           let vb1, vx = Builder.unpair varg in
           let vb12 = Builder.inj 0 vb1 b12 in
           let vb12x = Builder.pair vb12 vx in
           let v = Builder.pair vm vb12x in
           fun_arg_entry_block, [v])
      ];
    (* exit 2 *)
    let arg = Builder.begin_block access2.exit in
    let vm, vv = Builder.unpair arg in
    Builder.end_block_case vv
      [ (fun vres ->
            let vc, vd2 = Builder.unpair vres in
            let vy = join_code `Right vd2 y1 y2 y in
            let v = inject `Exit vm `Eval (Builder.pair vc vy) in
            access.exit, [v]);
        (fun vy2 ->
           lift_y2_access.exit, [vm; vy2]);
        (fun varg ->
           let vb2, vx = Builder.unpair varg in
           let vb12 = Builder.inj 1 vb2 b12 in
           let vb12x = Builder.pair vb12 vx in
           let v = Builder.pair vm vb12x in
           fun_arg_entry_block, [v])
      ];
    access
  | Cbvtype.Var, _, _
  | Cbvtype.Sgn (Cbvtype.Bool _), _, _
  | Cbvtype.Sgn (Cbvtype.Nat _), _, _
  | Cbvtype.Sgn (Cbvtype.Pair _), _, _
  | Cbvtype.Sgn (Cbvtype.Fun _), _, _ ->
    assert false

let rec translate (t: Cbvterm.t) : fragment =
  match t.t_desc with
  | Var x ->
    let id = "var" in
    let eval = fresh_eval id t in
    let access = fresh_access id t.t_type in
    (* eval *)
    let arg = Builder.begin_block eval.entry in
    let va, vgamma = Builder.unpair arg in
    let vx = build_context_lookup t.t_context x vgamma in
    let v = Builder.pair va vx in
    Builder.end_block_jump eval.exit [v];
    { eval = eval;
      access = access;
      context = [(x, access)]
    }
  | Contr(((x, a), xs), s) ->
    let s_fragment = translate s in
    let id = "contr" in
    let eval = {
      entry = fresh_label (id ^ "_eval_entry")
          [pairB t.t_ann (code_context t.t_context)];
      exit = s_fragment.eval.exit
    } in
    let x_access = fresh_access "contr" a in
    let tmult =
      let summands = List.map xs
          ~f:(fun x' -> Cbvtype.multiplicity
                 (List.Assoc.find_exn s.t_context x')) in
      match summands with
      | [] -> unitB
      | [x] -> x
      | xs -> Basetype.sumB xs in
    (* eval *)
    let arg = Builder.begin_block eval.entry in
    let vstack, vgamma = Builder.unpair arg in
    let delta =
      List.map s.t_context
        ~f:(fun (y, a) -> (if List.mem xs y then x else y), a) in
    let vdelta = build_context_map t.t_context delta vgamma in
    let v = Builder.pair vstack vdelta in
    Builder.end_block_jump s_fragment.eval.entry [v];
    (* project blocks *)
    begin
      match xs with
      | [] -> (* variable unused; dummy block *)
        let arg = Builder.begin_block x_access.exit in
        Builder.end_block_jump x_access.exit [arg]
      | [y] -> (* singleton: no sum type *)
        let arg = Builder.begin_block x_access.exit in
        let vd, vx = Builder.unpair arg in
        let vc = Builder.project vd tmult in
        let y_access = List.Assoc.find_exn s_fragment.context y in
        let v = Builder.pair vc vx in
        Builder.end_block_jump y_access.exit [v]
      | _ -> (* general case *)
        let arg = Builder.begin_block x_access.exit in
        let vd, vx = Builder.unpair arg in
        let vsum = Builder.project vd tmult in
        let target y =
          fun c ->
            let y_access = List.Assoc.find_exn s_fragment.context y in
            let v = Builder.pair c vx in
            y_access.exit, [v] in
        Builder.end_block_case vsum (List.map xs ~f:target)
    end;
    (* inject blocks *)
    begin
      match xs with
      | [] -> () (* no block needed *)
      | [y] -> (* singleton, no injection *)
        let y_access = List.Assoc.find_exn s_fragment.context y in
        let arg = Builder.begin_block y_access.entry in
        let vc, vx = Builder.unpair arg in
        let td, _ = unPairB_singleton x_access.entry.Ssa.arg_types in
        let vd = Builder.embed vc td in
        let v = Builder.pair vd vx in
        Builder.end_block_jump x_access.entry [v]
      | _ ->
        List.iteri xs
          ~f:(fun i y ->
              let y_access = List.Assoc.find_exn s_fragment.context y in
              let arg = Builder.begin_block y_access.entry in
              let vc, vx = Builder.unpair arg in
              let vin_c = Builder.inj i vc tmult in
              let td, _ = unPairB_singleton x_access.entry.Ssa.arg_types in
              let vd = Builder.embed vin_c td in
              let v = Builder.pair vd vx in
              Builder.end_block_jump x_access.entry [v])
    end;
    { eval = eval;
      access = s_fragment.access;
      context = (x, x_access) ::
                (List.filter s_fragment.context
                   ~f:(fun (x, _) -> not (List.mem xs x)))
    }
  | Const(Ast.Cboolconst b, []) ->
    let id = "boolconst" in
    let eval = fresh_eval id t in
    let access = fresh_access id t.t_type in
    (* eval *)
    let arg = Builder.begin_block eval.entry in
    let vstack = Builder.fst arg in
    let vi = Builder.boolconst b in
    let v = Builder.pair vstack vi in
    Builder.end_block_jump eval.exit [v];
    (* access *)
    let arg = Builder.begin_block access.entry in
    Builder.end_block_jump access.exit [arg];
    { eval = eval;
      access = access;
      context = []
    }
  | Const(Ast.Cintconst i, []) ->
    let id = "intconst" in
    let eval = fresh_eval id t in
    let access = fresh_access id t.t_type in
    (* eval *)
    let arg = Builder.begin_block eval.entry in
    let vstack = Builder.fst arg in
    let vi = Builder.intconst i in
    let v = Builder.pair vstack vi in
    Builder.end_block_jump eval.exit [v];
    (* access *)
    let arg = Builder.begin_block access.entry in
    Builder.end_block_jump access.exit [arg];
    { eval = eval;
      access = access;
      context = []
    }
  | Const(Ast.Cintconst _, _) ->
    assert false
  | Const(Ast.Cintprint, [s]) ->
    let s_fragment = translate s in
    let id = "intprint" in
    let eval = fresh_eval id t in
    let access = fresh_access id t.t_type in
    (* eval *)
    let arg = Builder.begin_block eval.entry in
    Builder.end_block_jump s_fragment.eval.entry [arg];
    (* print *)
    let arg = Builder.begin_block s_fragment.eval.exit in
    let vi = Builder.snd arg in
    ignore (Builder.primop (Ssa.Cintprint) vi);
    ignore (Builder.primop (Ssa.Cprint "\n") Builder.unit);
    Builder.end_block_jump eval.exit [arg];
    (* access entry *)
    let arg = Builder.begin_block access.entry in
    Builder.end_block_jump access.exit [arg];
    (* access exit *)
    let arg = Builder.begin_block s_fragment.access.exit in
    Builder.end_block_jump s_fragment.access.exit [arg];
    { eval = eval;
      access = access;
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
      | Ast.Cintlt -> "intlt", Ssa.Cintslt
      | Ast.Cboolconst _ -> assert false
      | Ast.Cintconst _ -> assert false
      | Ast.Cintprint -> assert false in
    let s1_fragment = translate s1 in
    let s2_fragment = translate s2 in
    let eval = fresh_eval id t in
    let access = fresh_access id t.t_type in
    (* eval 1 *)
    let arg = Builder.begin_block eval.entry in
    let vstack, vgamma = Builder.unpair arg in
    let vgamma1 = build_context_map t.t_context s1.t_context vgamma in
    let vgamma2 = build_context_map t.t_context s2.t_context vgamma in
    let vstack1 = Builder.embed (Builder.pair vstack vgamma2) s1.t_ann in
    let v = Builder.pair vstack1 vgamma1 in
    Builder.end_block_jump s1_fragment.eval.entry [v];
    (* eval 2 *)
    let arg = Builder.begin_block s1_fragment.eval.exit in
    let vstack1, vn1 = Builder.unpair arg in
    let vp = Builder.project vstack1
        (pairB t.t_ann (code_context s2.t_context)) in
    let vstack, vgamma2 = Builder.unpair vp in
    let vstack2 = Builder.embed (Builder.pair vstack vn1) s2.t_ann in
    let v = Builder.pair vstack2 vgamma2 in
    Builder.end_block_jump s2_fragment.eval.entry [v];
    (* eval 3 *)
    let arg = Builder.begin_block s2_fragment.eval.exit in
    let vstack2, vn2 = Builder.unpair arg in
    let vp = Builder.project vstack2 (pairB t.t_ann intB) in
    let vstack, vn1 = Builder.unpair vp in
    let veq = Builder.primop primop (Builder.pair vn1 vn2) in
    let v = Builder.pair vstack veq in
    Builder.end_block_jump eval.exit [v];
    (* access *)
    let arg = Builder.begin_block access.entry in
    Builder.end_block_jump access.exit [arg];
    (* dummy 1 *)
    let arg = Builder.begin_block s1_fragment.access.exit in
    Builder.end_block_jump s1_fragment.access.exit [arg];
    (* dummy 2 *)
    let arg = Builder.begin_block s2_fragment.access.exit in
    Builder.end_block_jump s2_fragment.access.exit [arg];
    { eval = eval;
      access = access;
      context = s1_fragment.context @ s2_fragment.context
    }
  | Const(_, _) ->
    assert false
  | Fun((x, xty), s) ->
    enter_stage (Cbvtype.multiplicity t.t_type);
    let s_fragment = translate s in
    leave_stage ();
    let id = "fun" in
    let eval = fresh_eval id t in
    let access = fresh_access id t.t_type in
    (* TODO: nimmt an, dass x im context von s vorkommt. *)
    let x_access = List.Assoc.find_exn s_fragment.context x in
    (* eval *)
    let arg = Builder.begin_block eval.entry in
    let vstack, vgamma = Builder.unpair arg in
    let vclosure = Builder.embed vgamma (Cbvtype.code t.t_type) in
    let v = Builder.pair vstack vclosure in
    Builder.end_block_jump eval.exit [v];
    (* invoke *)
    let invoke_block =
      let te = Cbvtype.multiplicity t.t_type in
      let ta = s.t_ann in
      let td = Cbvtype.code t.t_type in
      let tcx = Cbvtype.code xty in
      fresh_label "fun_decode" [te; pairB ta (pairB td tcx)] in
    let _ =
      let ve, vadx = Builder.begin_block2 invoke_block in
      let va, vdx = Builder.unpair vadx in
      let vd, vx = Builder.unpair vdx in
      let vgamma = Builder.project vd (code_context t.t_context) in
      let vgammax = Builder.pair vgamma vx in
      let vdelta = build_context_map ((x, xty)::t.t_context) s.t_context vgammax in
      (* TODO: Dokumentieren! *)
      let v = Builder.pair va vdelta in
      Builder.end_block_jump s_fragment.eval.entry [ve; v] in
    (* access *)
    let arg = Builder.begin_block access.entry in
    let ve = Builder.fst arg in
    let vreq = Builder.snd arg in
    Builder.end_block_case
      vreq
      [(fun c -> invoke_block, [ve; c]);
       (fun c -> s_fragment.access.entry, [ve; c]);
       (fun c -> x_access.exit, [ve; c])];
    (* s eval exit *)
    let ve, vv = Builder.begin_block2 s_fragment.eval.exit in
    let _, tf = unPairB_singleton access.exit.Ssa.arg_types in
    let vv0 = Builder.inj 0 vv tf in
    let v = Builder.pair ve vv0 in
    Builder.end_block_jump access.exit [v];
    (* s access exit *)
    let ve, vy = Builder.begin_block2 s_fragment.access.exit in
    let _(*te*), tf = unPairB_singleton access.exit.Ssa.arg_types in
    let vy1 = Builder.inj 1 vy tf in
    let v = Builder.pair ve vy1 in
    Builder.end_block_jump access.exit [v];
    (* s x_access entry *)
    let ve, vy = Builder.begin_block2 x_access.entry in
    let _(*te*), tf = unPairB_singleton access.exit.Ssa.arg_types in
    let vx2 = Builder.inj 2 vy tf in
    let v = Builder.pair ve vx2 in
    Builder.end_block_jump access.exit [v];
    let context =
      let gamma = List.filter s_fragment.context ~f:(fun (y, _) -> x <> y) in
      embed_context t.t_context gamma in
    { eval = eval;
      access = access;
      context = context
    }
  | Fix((th, f, x, xty), s) ->
    enter_stage th;
    let s_fragment = translate s in
    leave_stage ();
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
    (* eval *)
    let arg = Builder.begin_block eval.entry in
    let vstack, vgamma = Builder.unpair arg in
    let vclosure = Builder.embed vgamma (Cbvtype.code t.t_type) in
    let v = Builder.pair vstack vclosure in
    Builder.end_block_jump eval.exit [v];
    let eval_body_block =
      let ta = s.t_ann in
      let td = Cbvtype.code t.t_type in
      let tx = Cbvtype.code xty in
      fresh_label (id ^ "eval_body")
        [th; pairB ta (pairB td tx)] in
    let vh, vadx = Builder.begin_block2 eval_body_block in
    let va, vdx = Builder.unpair vadx in
    let vd, vx = Builder.unpair vdx in
    let vgamma = Builder.project vd (code_context t.t_context) in
    let vgammadx = Builder.pair (Builder.pair vgamma vd) vx in
    let vdelta = build_context_map
        ((x, xty) :: (f, t.t_type) :: t.t_context) s.t_context vgammadx in
    let v = (Builder.pair va vdelta) in
    Builder.end_block_jump s_fragment.eval.entry [vh; v];
    (* access *)
    let arg = Builder.begin_block access.entry in
    let ve, vreq = Builder.unpair arg in
    let vh = build_singleton ve in
    Builder.end_block_case
      vreq
      [ (fun c -> eval_body_block, [vh; c]);
        (fun c -> s_fragment.access.entry, [vh; c]);
        (fun c -> x_access.exit, [vh; c]) ];
    let invoke_rec_block =
      let t1 =
        match List.rev f_access.exit.Ssa.arg_types with
        | t1 :: _ -> t1
        | _ -> assert false in
      let _(*tg*), tans = unPairB t1 in
      fresh_label (id ^ "invoke_rec") [thg; tans] in
    let vhg, vm = Builder.begin_block2 invoke_rec_block in
    let vh, vg = Builder.unpair vhg in
    let v = Builder.pair vg vm in
    Builder.end_block_jump f_access.exit [vh; v];
    (* s eval exit *)
    let vh, vm = Builder.begin_block2 s_fragment.eval.exit in
    let _, ta = unPairB_singleton access.exit.Ssa.arg_types in
    let vm0 = Builder.inj 0 vm ta in
    let vcons = Builder.project vh tcons in
    Builder.end_block_case
      vcons
      [ (fun ve ->
            access.exit, [Builder.pair ve vm0]);
        (fun vhg ->
           invoke_rec_block, [vhg; vm0])
      ];
    (* s access exit *)
    let vh, vm = Builder.begin_block2 s_fragment.access.exit in
    let _, ta = unPairB_singleton access.exit.Ssa.arg_types in
    let vm1 = Builder.inj 1 vm ta in
    let vcons = Builder.project vh tcons in
    Builder.end_block_case
      vcons
      [ (fun ve ->
            access.exit, [Builder.pair ve vm1]);
        (fun vhg ->
           invoke_rec_block, [vhg; vm1])
      ];
    (* x access entry *)
    let vh, vm = Builder.begin_block2 x_access.entry in
    let _, ta = unPairB_singleton access.exit.Ssa.arg_types in
    let vm2 = Builder.inj 2 vm ta in
    let vcons = Builder.project vh tcons in
    Builder.end_block_case
      vcons
      [ (fun ve ->
            access.exit, [Builder.pair ve vm2]);
        (fun vhg ->
           invoke_rec_block, [vhg; vm2])
      ];
    (* f access entry *)
    let vh, vgm = Builder.begin_block2 f_access.entry in
    let vg, vm = Builder.unpair vgm in
    let vpushed = build_push vh vg in
    Builder.end_block_case
      vm
      [ (fun c -> eval_body_block, [vpushed; c]);
        (fun c -> s_fragment.access.entry, [vpushed; c]);
        (fun c -> x_access.exit, [vpushed; c])
      ];
    let context =
      let gamma = List.filter s_fragment.context
          ~f:(fun (y, _) -> y <> x && y <> f) in
      embed_context t.t_context gamma in
    { eval = eval;
      access = access;
      context = context
    }
  | Tailfix((th, f, x, xty), s) ->
    enter_stage th;
    let s_fragment = translate s in
    leave_stage ();
    let id = "tailfix" in
    let eval = fresh_eval id t in
    let access = fresh_access id t.t_type in
    let x_access = List.Assoc.find_exn s_fragment.context x in
    let f_access = List.Assoc.find_exn s_fragment.context f in
    let te, (_, ta, td, _) = Cbvtype.unFun t.t_type in
    let tea = pairB te ta in
    (* dummy *)
    let dummy_block = fresh_label (id ^ "dummy") [unitB] in
    let arg = Builder.begin_block dummy_block in
    Builder.end_block_jump dummy_block [arg];
    (* eval *)
    let arg = Builder.begin_block eval.entry in
    let vstack, vgamma = Builder.unpair arg in
    let vclosure = Builder.embed vgamma (Cbvtype.code t.t_type) in
    let v = Builder.pair vstack vclosure in
    Builder.end_block_jump eval.exit [v];
    let eval_body_block =
      let tx = Cbvtype.code xty in
      fresh_label (id ^ "eval_body") [te; pairB ta (pairB td tx)] in
    let ve, vadx = Builder.begin_block2 eval_body_block in
    let va, vdx = Builder.unpair vadx in
    let vd, vx = Builder.unpair vdx in
    let vgamma = Builder.project vd (code_context t.t_context) in
    let vgammadx = Builder.pair (Builder.pair vgamma vd) vx in
    let vdelta = build_context_map
        ((x, xty) :: (f, t.t_type) :: t.t_context) s.t_context vgammadx in
    let vh = Builder.embed (Builder.pair ve va) th in
    let vu = Builder.embed Builder.unit s.t_ann in
    let v = Builder.pair vu vdelta in
    Builder.end_block_jump s_fragment.eval.entry [vh; v];
    (* access *)
    let arg = Builder.begin_block access.entry in
    let ve, vreq = Builder.unpair arg in
    Builder.end_block_case
      vreq
      [ (fun c -> eval_body_block, [ve; c]);
        (fun c -> dummy_block, [Builder.unit]);
        (fun c -> dummy_block, [Builder.unit]) ];
    (* s eval exit *)
    let vh, vum = Builder.begin_block2 s_fragment.eval.exit in
    let vm = Builder.snd vum in
    let vea = Builder.project vh tea in
    let ve = Builder.fst vea in
    let va = Builder.snd vea in
    let _, tans = unPairB_singleton access.exit.Ssa.arg_types in
    let vm0 = Builder.inj 0 (Builder.pair va vm) tans in
    Builder.end_block_jump access.exit [Builder.pair ve vm0];
    (* s access exit *)
    let _ = Builder.begin_block2 s_fragment.access.exit in
    Builder.end_block_jump (dummy_block) [Builder.unit];
    (* x access entry *)
    let _ = Builder.begin_block2 x_access.entry in
    Builder.end_block_jump (dummy_block) [Builder.unit];
    (* f access entry *)
    let vh, vgm = Builder.begin_block2 f_access.entry in
    let vea = Builder.project vh tea in
    let ve = Builder.fst vea in
    let va = Builder.snd vea in
    let _, vm = Builder.unpair vgm in
    Builder.end_block_case
      vm
      [ (fun c -> eval_body_block,
                  [ve; Builder.pair va (Builder.snd c)]);
        (fun c -> dummy_block, [Builder.unit]);
        (fun c -> dummy_block, [Builder.unit]) ];
    let context =
      let gamma = List.filter s_fragment.context
          ~f:(fun (y, _) -> y <> x && y <> f) in
      embed_context t.t_context gamma in
    { eval = eval;
      access = access;
      context = context
    }
  | Pair(t1, t2) ->
    let t1_fragment = translate t1 in
    let t2_fragment = translate t2 in
    let id = "pair" in
    let eval = fresh_eval id t in
    let access = fresh_access id t.t_type in
    (* evaluation blocks *)
    (* block 1 *)
    let arg = Builder.begin_block eval.entry in
    let vu, vgammadelta = Builder.unpair arg in
    let vgamma = build_context_map t.t_context t1.t_context vgammadelta in
    let vdelta = build_context_map t.t_context t2.t_context vgammadelta in
    let embed_val = Builder.embed (Builder.pair vu vdelta) t1.t_ann in
    let v = Builder.pair embed_val vgamma in
    Builder.end_block_jump t1_fragment.eval.entry [v];
    (* block 2 *)
    let arg = Builder.begin_block t1_fragment.eval.exit in
    let ve, vf = Builder.unpair arg in
    let vu_delta = Builder.project ve
        (pairB t.t_ann (code_context t2.t_context)) in
    let vu, vdelta = Builder.unpair vu_delta in
    let vu_f = Builder.pair vu vf in
    let ve' = Builder.embed vu_f t2.t_ann in
    let v = Builder.pair ve' vdelta in
    Builder.end_block_jump t2_fragment.eval.entry [v];
    (* block 3*)
    let arg = Builder.begin_block t2_fragment.eval.exit in
    let ve, v2 = Builder.unpair arg in
    let vu_f = Builder.project ve (pairB t.t_ann (Cbvtype.code t1.t_type)) in
    let vu, v1 = Builder.unpair vu_f in
    let v = Builder.pair vu (Builder.pair v1 v2) in
    Builder.end_block_jump eval.exit [v];
    let outer_multiplicity, inner_access_entry = unPairB_singleton access.entry.Ssa.arg_types in
    let left_inner_access_entry, right_inner_access_entry =
      match Basetype.case inner_access_entry with
      | Basetype.Var -> assert false
      | Basetype.Sgn s ->
        match s with
        | Basetype.DataB(_, [l; r]) -> l, r
        | _ -> assert false in
    (* acces entry 1 *)
    let access_entry1 =
      let tm, tq = unPairB left_inner_access_entry in
      fresh_label "pair_access1" [outer_multiplicity; pairB tm tq] in
    let v_mult, vq = Builder.begin_block2 access_entry1 in
    let v_inner_mult = Builder.fst vq in
    let v_inner_q = Builder.snd vq in
    let t1_multiplicty, _ = unPairB_singleton t1_fragment.access.entry.Ssa.arg_types in
    let vm = Builder.embed (Builder.pair v_mult v_inner_mult) t1_multiplicty in
    let v = Builder.pair vm v_inner_q in
    Builder.end_block_jump t1_fragment.access.entry [v];
    (* acces entry 2 *)
    let access_entry2 =
      let tm, tq = unPairB right_inner_access_entry in
      fresh_label "pair_access2" [outer_multiplicity; pairB tm tq] in
    let v_mult, vq = Builder.begin_block2 access_entry2 in
    let v_inner_mult = Builder.fst vq in
    let v_inner_q = Builder.snd vq in
    let t2_multiplicty, _ = unPairB_singleton t2_fragment.access.entry.Ssa.arg_types in
    let vm = Builder.embed (Builder.pair v_mult v_inner_mult) t2_multiplicty in
    let v = Builder.pair vm v_inner_q in
    Builder.end_block_jump t2_fragment.access.entry [v];
    (* acces pair *)
    let arg = Builder.begin_block access.entry in
    let vm = Builder.fst arg in
    let vq = Builder.snd arg in
    Builder.end_block_case
      vq
      [ (fun c -> access_entry1, [vm; c]);
        (fun c -> access_entry2, [vm; c]) ];
    let _, inner_access_exit = unPairB_singleton access.exit.Ssa.arg_types in
    (* access exit 1 *)
    let arg = Builder.begin_block t1_fragment.access.exit in
    let tm, _ = unPairB left_inner_access_entry in
    let vm1 = Builder.fst arg in
    let va = Builder.snd arg in
    let vm = Builder.project vm1 (pairB outer_multiplicity tm) in
    let vmo = Builder.fst vm in
    let vmi = Builder.snd vm in
    let vi = Builder.inj 0 (Builder.pair vmi va) inner_access_exit in
    let v = Builder.pair vmo vi in
    Builder.end_block_jump access.exit [v];
    (* access exit 2 *)
    let arg = Builder.begin_block t2_fragment.access.exit in
    let tm, _ = unPairB right_inner_access_entry in
    let vm1 = Builder.fst arg in
    let va = Builder.snd arg in
    let vm = Builder.project vm1 (pairB outer_multiplicity tm) in
    let vmo = Builder.fst vm in
    let vmi = Builder.snd vm in
    let vi = Builder.inj 1 (Builder.pair vmi va) inner_access_exit in
    let v = Builder.pair vmo vi in
    Builder.end_block_jump access.exit [v];
    { eval = eval;
      access = access;
      context = t1_fragment.context @ t2_fragment.context
    }
  | Fst(t1) ->
    let t1_fragment = translate t1 in
    let id = "fst" in
    let eval = fresh_eval id t in
    let access = fresh_access id t.t_type in
    (* evaluation blocks *)
    (* block 1 *)
    let arg = Builder.begin_block eval.entry in
    Builder.end_block_jump t1_fragment.eval.entry [arg];
    (* block 2 *)
    let arg = Builder.begin_block t1_fragment.eval.exit in
    let vm, vp = Builder.unpair arg in
    let vp1 = Builder.fst vp in
    let v = Builder.pair vm vp1 in
    Builder.end_block_jump eval.exit [v];
    (* access entry *)
    let arg = Builder.begin_block access.entry in
    let vu = Builder.unit in
    let tm, tq = unPairB_singleton t1_fragment.access.entry.Ssa.arg_types in
    let vm = Builder.embed vu tm in
    let vq = Builder.inj 0 arg tq in
    let v = Builder.pair vm vq in
    Builder.end_block_jump t1_fragment.access.entry [v];
    let assert_false =
      fresh_label "assert_false" [unitB] in
    let _ =
      let l = assert_false in
      let arg = Builder.begin_block l in
      Builder.end_block_jump l [arg] in
    (* access exit *)
    let arg = Builder.begin_block t1_fragment.access.exit in
    let va = Builder.snd arg in
    Builder.end_block_case
      va
      [ (fun c -> access.exit, [c]);
        (fun _ -> assert_false, [Builder.unit]) ];
    { eval = eval;
      access = access;
      context = t1_fragment.context
    }
  | Snd(t1) ->
    let t1_fragment = translate t1 in
    let id = "snd" in
    let eval = fresh_eval id t in
    let access = fresh_access id t.t_type in
    (* evaluation blocks *)
    (* block 1 *)
    let arg = Builder.begin_block eval.entry in
    Builder.end_block_jump t1_fragment.eval.entry [arg];
    (* block 2 *)
    let arg = Builder.begin_block t1_fragment.eval.exit in
    let vm, vp = Builder.unpair arg in
    let vp2 = Builder.snd vp in
    let v = Builder.pair vm vp2 in
    Builder.end_block_jump eval.exit [v];
    (* access entry *)
    let arg = Builder.begin_block access.entry in
    let vu = Builder.unit in
    let tm, tq = unPairB_singleton t1_fragment.access.entry.Ssa.arg_types in
    let vm = Builder.embed vu tm in
    let vq = Builder.inj 1 arg tq in
    let v = Builder.pair vm vq in
    Builder.end_block_jump t1_fragment.access.entry [v];
    let assert_false =
      fresh_label "assert_false" [unitB] in
    let l = assert_false in
    let arg = Builder.begin_block l in
    Builder.end_block_jump l [arg];
    (* access exit *)
    let arg = Builder.begin_block t1_fragment.access.exit in
    let va = Builder.snd arg in
    Builder.end_block_case
      va
      [ (fun _ -> assert_false, [Builder.unit]) ;
        (fun c -> access.exit, [c]) ];
    { eval = eval;
      access = access;
      context = t1_fragment.context
    }
  | App(t1, t2) ->
    let t1_fragment = translate t1 in
    let t2_fragment = translate t2 in
    let id = "app" in
    let eval = fresh_eval id t in
    let access = fresh_access id t.t_type in
    (* block 1 *)
    let arg = Builder.begin_block eval.entry in
    let vu, vgammadelta = Builder.unpair arg in
    let vgamma = build_context_map t.t_context t1.t_context vgammadelta in
    let vdelta = build_context_map t.t_context t2.t_context vgammadelta in
    let embed_val = Builder.embed (Builder.pair vu vdelta) t1.t_ann in
    let v = Builder.pair embed_val vgamma in
    Builder.end_block_jump t1_fragment.eval.entry [v];
    (* block 2 *)
    let arg = Builder.begin_block t1_fragment.eval.exit in
    let ve, vf = Builder.unpair arg in
    let vu_delta = Builder.project ve
        (pairB t.t_ann (code_context t2.t_context)) in
    let vu, vdelta = Builder.unpair vu_delta in
    let vu_f = Builder.pair vu vf in
    let ve' = Builder.embed vu_f t2.t_ann in
    let v = Builder.pair ve' vdelta in
    Builder.end_block_jump t2_fragment.eval.entry [v];
    (* block 3 *)
    let arg = Builder.begin_block t2_fragment.eval.exit in
    let ve, vx = Builder.unpair arg in
    let vu_f = Builder.project ve (pairB t.t_ann (Cbvtype.code t1.t_type)) in
    let vu, vf = Builder.unpair vu_f in
    let _, (_, tv, _, _) = Cbvtype.unFun t1.t_type in
    let vv = Builder.embed vu tv in
    let vvfx = Builder.pair vv (Builder.pair vf vx) in
    let td, tfunacc = unPairB_singleton t1_fragment.access.entry.Ssa.arg_types in
    let vfunacc = Builder.inj 0 vvfx tfunacc in
    let vd = Builder.embed Builder.unit td in
    let v = Builder.pair vd vfunacc in
    Builder.end_block_jump t1_fragment.access.entry [v];
    (* block 5 *)
    let arg = Builder.begin_block access.entry in
    let td, tfunacc = unPairB_singleton t1_fragment.access.entry.Ssa.arg_types in
    let vd = Builder.embed Builder.unit td in
    let v = Builder.pair vd (Builder.inj 1 arg tfunacc) in
    Builder.end_block_jump t1_fragment.access.entry [v];
    (* block 7 *)
    let arg = Builder.begin_block t2_fragment.access.exit in
    let td, tfunacc = unPairB_singleton t1_fragment.access.entry.Ssa.arg_types in
    let vd = Builder.embed Builder.unit td in
    let v = Builder.pair vd (Builder.inj 2 arg tfunacc) in
    Builder.end_block_jump t1_fragment.access.entry [v];
    (* block 8 *)
    let block8 =
      let _, (_, tv, _, _) = Cbvtype.unFun t1.t_type in
      let _, tres = unPairB_singleton eval.exit.Ssa.arg_types in
      fresh_label "decode_stack" [pairB tv tres] in
    let arg = Builder.begin_block block8 in
    let vv, vres = Builder.unpair arg in
    let vu = Builder.project vv t.t_ann in
    let v = Builder.pair vu vres in
    Builder.end_block_jump eval.exit [v];
    (* case block *)
    let arg = Builder.begin_block t1_fragment.access.exit in
    let vfun = Builder.snd arg in
    Builder.end_block_case
      vfun
      [ (fun c -> block8, [c]);
        (fun c -> access.exit, [c]);
        (fun c -> t2_fragment.access.entry, [c]) ];
    { eval = eval;
      access = access;
      context = t1_fragment.context @ t2_fragment.context
    }
  | Ifz(tc, t1, t2) ->
    let tc_fragment = translate tc in
    let t1_fragment = translate t1 in
    let t2_fragment = translate t2 in
    let id = "if" in
    let eval = fresh_eval id t in
    (* eval 1 *)
    let arg = Builder.begin_block eval.entry in
    let vstack, vgamma = Builder.unpair arg in
    let vgammac = build_context_map t.t_context tc.t_context vgamma in
    let vgamma1 = build_context_map t.t_context t1.t_context vgamma in
    let vgamma2 = build_context_map t.t_context t2.t_context vgamma in
    let vstack1 = Builder.embed (Builder.pair vstack (Builder.pair vgamma1 vgamma2)) tc.t_ann in
    let v = Builder.pair vstack1 vgammac in
    Builder.end_block_jump tc_fragment.eval.entry [v];
    (* eval c *)
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
      [ (fun _ -> t1_fragment.eval.entry, [Builder.pair vstack vgamma1]);
        (fun _ -> t2_fragment.eval.entry, [Builder.pair vstack vgamma2]) ];
    (* eval rt *)
    let arg = Builder.begin_block t1_fragment.eval.exit in
    let vstack = Builder.fst arg in
    let vn = Builder.snd arg in
    let v = Builder.pair vstack (join_code `Left vn t1.t_type t2.t_type t.t_type) in
    Builder.end_block_jump eval.exit [v];
    (* eval rf *)
    let arg = Builder.begin_block t2_fragment.eval.exit in
    let vstack = Builder.fst arg in
    let vn = Builder.snd arg in
    let v = Builder.pair vstack (join_code `Right vn t1.t_type t2.t_type t.t_type) in
    Builder.end_block_jump eval.exit [v];
    (* access c *)
    let arg = Builder.begin_block tc_fragment.access.exit in
    Builder.end_block_jump tc_fragment.access.exit [arg];
    let access =
      join
        (t1_fragment.access, t1.t_type)
        (t2_fragment.access, t2.t_type)
        t.t_type in
    { eval = eval;
      access = access;
      context = tc_fragment.context @ t1_fragment.context @ t2_fragment.context
    }

let to_ssa t =
  Builder.reset();
  let f = translate t in
  let ret_ty = List.hd_exn f.eval.exit.Ssa.arg_types in
  (* return *)
  let arg = Builder.begin_block f.eval.exit in
  Builder.end_block_return arg;
  (* access exit *)
  let arg = Builder.begin_block f.access.exit in
  Builder.end_block_jump f.access.exit [arg];
  let visited = Ident.Table.create () in
  let rev_sorted_blocks = ref [] in
  let rec sort_blocks i =
    if not (Ident.Table.mem visited i) then
      begin
        (* Printf.printf "%s\n" (Ident.to_string i); *)
        Ident.Table.set visited ~key:i ~data:();

        let b = Ident.Table.find_exn Builder.blocks i in
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
