open Core_kernel.Std
open Cbvterm

module Builder = Ssabuilder

let pairB (a1: Basetype.t) (a2: Basetype.t): Basetype.t =
  Basetype.newty (Basetype.TupleB [a1; a2])

let fresh_label stage (name: string) (a : Basetype.t list): Ssa.label =
  { Ssa.name = Ident.fresh name;
    Ssa.arg_types = (List.rev stage) @ a }

(* TODO: this is leaky *)
module Access : sig
  type t =
      Base
    | Pair of Basetype.t * t * t
    | Fun of Basetype.t * Basetype.t * Basetype.t * Ssa.label * t * t

  val iter2_exn: t -> t ->
    f:((Ssa.label * Basetype.t list) -> (Ssa.label * Basetype.t list) -> unit) -> unit

  val iter2_list_exn: t -> t list ->
    f:((Ssa.label * Basetype.t list) -> (Ssa.label * Basetype.t list) list -> unit) -> unit

  val forward: t -> t -> unit
  val unreachable: t -> unit

  val project_split: t -> t list -> unit
  val join_embed: t list -> t -> unit

  val project_push: t -> t -> unit
  val pop_embed: t -> t -> unit

  val push_unit_embed: t -> t -> unit
  val pop_discard: t -> t -> unit

  val fresh_entry: Basetype.t list -> string -> Cbvtype.t -> t
  val fresh_exit: Basetype.t list -> string -> Cbvtype.t -> t
end =
struct
  type t =
      Base
    | Pair of Basetype.t * t * t
    | Fun of Basetype.t * Basetype.t * Basetype.t * Ssa.label * t * t

  let labels (a : t) : (Ssa.label * Basetype.t list) list =
    let rec ls (a : t) (ms) : (Ssa.label * (Basetype.t list)) list =
      match a with
      | Base -> []
      | Pair(m, x, y) ->
        (ls x (m :: ms)) @ (ls y (m :: ms))
      | Fun(m, s, c, app, x, y) ->
        let stage' = m :: ms in
        (app, List.rev stage') :: (ls x stage') @ (ls y stage') in
    ls a []

  let iter a = List.iter (labels a)

  let iter2_exn a b ~f:f  =
    List.iter2_exn (labels a) (labels b) ~f:f

  let iter2_list_exn a xs ~f:f  =
    let ls = List.map ~f:labels xs |> List.transpose_exn in
    List.iter2_exn (labels a) ls ~f:f

  let forward_with a b ~f:f : unit =
    iter2_exn a b
      ~f:(fun (la, ma) (lb, mb) ->
        let da = List.length ma + 1 in
        let arg = Builder.begin_blockn da la in
        f arg (lb, mb))

  let forward a b : unit =
    forward_with a b ~f:(fun arg (lb, _) -> Builder.end_block_jump lb arg)

  let unreachable a : unit =
    iter a
      ~f:(fun (l, _) ->
        ignore (Builder.begin_block l);
        Builder.end_block_unreachable ())

  (* Gamma |- C.X to Gamma |- A1.X, ..., Gamma |- An.X where A1*...*An <= C *)
  let project_split a al : unit =
    iter2_list_exn a al
      ~f:(fun (la, ma) ls ->
        let dsts, mults = List.unzip ls in
        let outermults = List.map ~f:List.hd_exn mults in
        let tsum = Basetype.sumB outermults in
        let da = List.length ma + 1 in
        match Builder.begin_blockn da la with
        | [] -> assert false
        | vm :: vv ->
          let vm' = Builder.project vm tsum in
          let cases = List.map dsts ~f:(fun dst ->
            fun c -> dst, c :: vv) in
          Builder.end_block_case vm' cases
      )

  (* Gamma |- A1.X, ..., Gamma |- An.X to Gamma |- C.X where A1*...*An <= C *)
  let join_embed al a : unit =
    iter2_list_exn a al
      ~f:(fun (dst, dst_mults) ls ->
        let srcs, mults = List.unzip ls in
        let outermults = List.map ~f:List.hd_exn mults in
        let tsum = Basetype.sumB outermults in
        List.iteri ls
          ~f:(fun i (src, src_mults) ->
            let n = List.length src_mults + 1 in
            match Builder.begin_blockn n src, dst_mults with
            | vm :: vv, dst_outermult :: _ ->
              let vi = Builder.inj i vm tsum in
              let vm' = Builder.embed vi dst_outermult in
              Builder.end_block_jump dst (vm' :: vv)
            | _ -> assert false
          )
      )

  (* Gamma |- C.X to Gamma, A |- B.X where A*B <= C *)
  let project_push a b : unit =
    iter2_exn a b
      ~f:(fun (la, ma) (lb, mb) ->
        let da = List.length ma + 1 in
        let db = List.length mb + 1 in
        match Builder.begin_blockn da la, mb with
        | vc :: vv, tb :: _ ->
          (* ta is the first type in the context *)
          let ta = List.last_exn
                     (List.take (List.rev lb.Ssa.arg_types) (db + 1)) in
          let vm' = Builder.project vc (pairB ta tb) in
          let va, vb = Builder.unpair vm' in
          Builder.end_block_jump lb (va :: vb :: vv)
        | _ -> assert false
      )

  (* Gamma, A |- B.X to Gamma |- C.X where A*B <= C *)
  let pop_embed a b : unit =
    iter2_exn a b
      ~f:(fun (la, ma) (lb, mb) ->
        let da = List.length ma + 1 in
        match Builder.begin_blockn (da + 1) la, mb with
        | va :: vb :: vv, tc :: _ ->
          let vc = Builder.embed (Builder.pair va vb) tc in
          Builder.end_block_jump lb (vc:: vv)
        | _ -> assert false
      )

  (* Gamma, C |- A.X to Gamma |- A.X where unit <= C *)
  let pop_discard a b : unit =
    iter2_exn a b
      ~f:(fun (la, ma) (lb, mb) ->
        let da = List.length ma + 1 in
        match Builder.begin_blockn (da + 1) la with
        | _ :: vv ->
          Builder.end_block_jump lb vv
        | _ -> assert false
      )

  (* Gamma |- A.X to Gamma, C |- A.X where unit <= C *)
  let push_unit_embed a b : unit =
    iter2_exn a b
      ~f:(fun (la, ma) (lb, mb) ->
        let da = List.length ma + 1 in
        let db = List.length mb + 1 in
        let vv = Builder.begin_blockn da la in
        let tc = List.last_exn
                   (List.take (List.rev lb.Ssa.arg_types) (db + 1)) in
        let vc = Builder.embed Builder.unit tc in
        Builder.end_block_jump lb (vc :: vv)
      )

  let rec fresh_entry (stage: Basetype.t list) (n: string) (a: Cbvtype.t): t =
    match Cbvtype.case a with
    | Cbvtype.Var -> failwith "var"
    | Cbvtype.Sgn s ->
      match s with
      | Cbvtype.Bool(m) -> Base
      | Cbvtype.Nat(m) -> Base
      | Cbvtype.Pair(m, (x, y)) ->
        let xentry = fresh_entry (m :: stage) n x in
        let yentry = fresh_entry (m :: stage) n y in
        Pair(m, xentry, yentry)
      | Cbvtype.Fun(m, (x, s, c, y)) ->
        let xc = Cbvtype.code x in
        let yentry = fresh_entry (m :: stage) n y in
        let xexit = fresh_exit (m :: stage) n x in
        let eval = fresh_label (m :: stage) (n ^ "_access_entry") [pairB s (pairB c xc)] in
        Fun(m, s, c, eval, xexit, yentry)
  and fresh_exit (stage: Basetype.t list) (n: string) (a: Cbvtype.t): t =
    match Cbvtype.case a with
    | Cbvtype.Var -> failwith "var"
    | Cbvtype.Sgn s ->
      match s with
      | Cbvtype.Bool(m) -> Base
      | Cbvtype.Nat(m) -> Base
      | Cbvtype.Pair(m, (x, y)) ->
        let xexit = fresh_exit (m :: stage) n x in
        let yexit = fresh_exit (m :: stage) n y in
        Pair(m, xexit, yexit)
      | Cbvtype.Fun(m, (x, s, c, y)) ->
        let yc = Cbvtype.code y in
        let yexit = fresh_exit (m :: stage) n y in
        let xentry = fresh_entry (m :: stage) n x in
        let ret = fresh_label (m :: stage) (n ^ "_access_exit") [pairB s yc] in
        Fun(m, s, c, ret, xentry, yexit)
end

module Context =
struct
  let code (gamma : Cbvtype.t Typing.context) : Basetype.t =
    let cs = List.map ~f:(fun (_, a) -> Cbvtype.code a) gamma in
    Basetype.newty (Basetype.TupleB cs)

  let decode (v: Builder.value) (gamma : Cbvtype.t Typing.context)
    : (Builder.value Typing.context) =
    let vv, va = v in
    assert (Basetype.equals va (code gamma));
    List.mapi gamma ~f:(fun i (x, _) -> x, Builder.proj v i)

  let encode (vs: Builder.value Typing.context) (gamma : Cbvtype.t Typing.context)
    : Builder.value =
    let vs =
      List.map gamma ~f:(fun (x, a) ->
          let vx = List.Assoc.find_exn vs x in
          assert (Basetype.equals (snd vx) (Cbvtype.code a));
          vx) in
    Builder.tuple vs

  let rec build_lookup
      (gamma: Cbvtype.t Typing.context)
      (x: Ident.t)
      (v: Builder.value)
    : Builder.value =
    let vs = decode v gamma in
    List.Assoc.find_exn vs x

  let build_map
        (gamma: Cbvtype.t Typing.context)
        (delta: Cbvtype.t Typing.context)
        (code_gamma: Builder.value)
    : Builder.value =
    let vs = decode code_gamma gamma in
    encode vs delta
end

type 'a interface = {
  entry: 'a;
  exit: 'a
}

type int_interface = Ssa.label interface
type access_interface = Access.t interface

type term_with_interface = {
  desc: (term_with_interface, Cbvtype.t) Cbvterm.sgn;
  eval: int_interface;
  access: access_interface;
  context: (Ident.t * access_interface) list;
  term: Cbvterm.t;
}

let block_name_of_term (t: Cbvterm.t) : string =
  let open Ast.Location in
  match t.t_loc with
  | Some l ->
    Printf.sprintf "_l%i_c%i" l.start_pos.line l.start_pos.column
  | None ->
    ""

let fresh_eval (stage: Basetype.t list) (t: Cbvterm.t) : int_interface =
  let s = block_name_of_term t in
  { entry = fresh_label stage (s ^ "_eval_entry") [pairB t.t_ann (Context.code t.t_context)];
    exit  = fresh_label stage (s ^ "_eval_exit") [pairB t.t_ann (Cbvtype.code t.t_type)] }

let fresh_access_named (stage: Basetype.t list) (n : string) (a : Cbvtype.t) : access_interface =
  { entry = Access.fresh_entry stage n a;
    exit = Access.fresh_exit stage n a }

let fresh_access (stage: Basetype.t list) (t: Cbvterm.t) : access_interface =
  let n = block_name_of_term t in
  fresh_access_named stage n t.t_type

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
let rec embed_context_int
          (stage : Basetype.t list)
          (outer : Cbvtype.t Typing.context)
          (inner : access_interface Typing.context)
  : access_interface Typing.context =
  List.map inner ~f:(
    fun (y, _) ->
      (y, fresh_access_named stage "context" (List.Assoc.find_exn outer y))
  )

let rec add_interface (stage : Basetype.t list) (t : Cbvterm.t)
  : term_with_interface =
  match t.t_desc with
  | Var x ->
    let eval = fresh_eval stage t in
    let access = fresh_access stage t in
    { desc = Var x;
      eval = eval;
      access = access;
      context = [(x, access)];
      term = t
    }
  | Contr(((x, a), xs), s) ->
    let si = add_interface stage s in
    let eval = fresh_eval stage t in
    let x_access = fresh_access_named stage "contr" a in
    { desc = Contr(((x, a), xs), si);
      eval = eval;
      access = si.access;
      context = (x, x_access) ::
                (List.filter si.context
                   ~f:(fun (x, _) -> not (List.mem xs x)));
      term = t
    }
  | Const(Ast.Cboolconst b, []) ->
    let eval = fresh_eval stage t in
    let access = fresh_access stage t in
    { desc = Const(Ast.Cboolconst b, []);
      eval = eval;
      access = access;
      context = [];
      term = t
    }
  | Const(Ast.Cintconst i, []) ->
    let eval = fresh_eval stage t in
    let access = fresh_access stage t in
    { desc = Const(Ast.Cintconst i, []);
      eval = eval;
      access = access;
      context = [];
      term = t
    }
  | Const(Ast.Cintconst _, _) ->
    assert false
  | Const(Ast.Cintprint, [s]) ->
    let si = add_interface stage s in
    let eval = fresh_eval stage t in
    let access = fresh_access stage t in
    { desc = Const(Ast.Cintprint, [si]);
      eval = eval;
      access = access;
      context = si.context;
      term = t
    }
  | Const(Ast.Cintprint, _) ->
    assert false
  | Const(c, [s1; s2]) ->
    let s1i = add_interface stage s1 in
    let s2i = add_interface stage s2 in
    let eval = fresh_eval stage t in
    let access = fresh_access stage t in
    { desc = Const(c, [s1i; s2i]);
      eval = eval;
      access = access;
      context = s1i.context @ s2i.context;
      term = t;
    }
  | Const(_, _) ->
    assert false
  | Fun((x, xty), s) ->
    let inner_stage = Cbvtype.multiplicity t.t_type :: stage in
    let si = add_interface inner_stage s in
    let eval = fresh_eval stage t in
    let access = fresh_access stage t in
    let context =
      let gamma = List.filter si.context ~f:(fun (y, _) -> x <> y) in
      embed_context_int stage t.t_context gamma in
    { desc = Fun((x, xty), si);
      eval = eval;
      access = access;
      context = context;
      term = t
    }
  | Fix((th, f, x, xty), s) ->
    let si = add_interface (th :: stage) s in
    let eval = fresh_eval stage t in
    let access = fresh_access stage t in
    let context =
      let gamma = List.filter si.context ~f:(fun (y, _) -> y <> x && y <> f) in
      embed_context_int stage t.t_context gamma in
    { desc = Fix((th, f, x, xty), si);
      eval = eval;
      access = access;
      context = context;
      term = t
    }
  | Tailfix((th, f, x, xty), s) ->
    let si = add_interface (th :: stage) s in
    let eval = fresh_eval stage t in
    let access = fresh_access stage t in
    let context = let gamma = List.filter si.context
          ~f:(fun (y, _) -> y <> x && y <> f) in
      embed_context_int stage t.t_context gamma in
    { desc = Tailfix((th, f, x, xty), si);
      eval = eval;
      access = access;
      context = context;
      term = t
    }
  | Pair(t1, t2) ->
    let t1i = add_interface stage t1 in
    let t2i = add_interface stage t2 in
    let eval = fresh_eval stage t in
    let access = fresh_access stage t in
    { desc = Pair(t1i, t2i);
      eval = eval;
      access = access;
      context = t1i.context @ t2i.context;
      term = t
    }
  | Fst(t1) ->
    let t1i = add_interface stage t1 in
    let eval = fresh_eval stage t in
    let access = fresh_access stage t in
    { desc = Fst(t1i);
      eval = eval;
      access = access;
      context = t1i.context;
      term = t
    }
  | Snd(t1) ->
    let t1i = add_interface stage t1 in
    let eval = fresh_eval stage t in
    let access = fresh_access stage t in
    { desc = Snd(t1i);
      eval = eval;
      access = access;
      context = t1i.context;
      term = t
    }
  | App(t1, t2) ->
    let t1i = add_interface stage t1 in
    let t2i = add_interface stage t2 in
    let eval = fresh_eval stage t in
    let access = fresh_access stage t in
    { desc = App(t1i, t2i);
      eval = eval;
      access = access;
      context = t1i.context @ t2i.context;
      term = t
    }
  | Ifz(tc, t1, t2) ->
    let tci = add_interface stage tc in
    let t1i = add_interface stage t1 in
    let t2i = add_interface stage t2 in
    let eval = fresh_eval stage t in
    let access = fresh_access_named stage "join" t.t_type in
    { desc = Ifz(tci, t1i, t2i);
      eval = eval;
      access = access;
      context = tci.context @ t1i.context @ t2i.context;
      term = t
    }


let rec project_context
    (outer : access_interface Typing.context)
    (inner : access_interface Typing.context)
  : unit =
  List.iter inner
    ~f:(fun (y, y_access) ->
      let y_outer_access = List.Assoc.find_exn outer y in
      Access.project_push y_outer_access.exit y_access.exit)

let rec embed_context
    (outer : access_interface Typing.context)
    (inner : access_interface Typing.context)
  : unit =
  List.iter inner
    ~f:(fun (y, y_access) ->
      let y_outer_access = List.Assoc.find_exn outer y in
      Access.pop_embed y_access.entry y_outer_access.entry)

(* TODO: still ugly!! *)
let rec join_code k v a1 a2 a =
  let i = match k with
    | `Left -> 0
    | `Right -> 1 in
  match a, a1, a2 with
  | Access.Base, Access.Base, Access.Base -> v
  | Access.Pair(_, x, y), Access.Pair(_, x1, y1), Access.Pair(_, x2, y2) ->
    let vx, vy = Builder.unpair v in
    let vx' = join_code k vx x1 x2 x in
    let vy' = join_code k vy y1 y2 y in
    Builder.pair vx' vy'
  | Access.Fun(_, _, d, _, _, _),
    Access.Fun(_, _, d1, _, _, _),
    Access.Fun(_, _, d2, _, _, _) ->
    let vi = Builder.inj i v (Basetype.sumB [d1; d2]) in
    Builder.embed vi d
  | Access.Base, _, _
  | Access.Pair _, _, _
  | Access.Fun _, _, _ ->
    assert false

let rec split_entry a a1 a2 : unit =
  match a, a1, a2 with
  | Access.Base, Access.Base, Access.Base -> ()
  | Access.Pair(m, x, y), Access.Pair(m1, x1, y1), Access.Pair(m2, x2, y2) ->
    assert (Basetype.equals m m1);
    assert (Basetype.equals m m2);
    split_entry x x1 x2;
    split_entry y y1 y2
  | Access.Fun(m, s, d, eval, x, y),
    Access.Fun(m1, s1, d1, eval1, x1, y1),
    Access.Fun(m2, s2, d2, eval2, x2, y2) ->
    assert (Basetype.equals m m1);
    assert (Basetype.equals m m2);
    assert (Basetype.equals s s1);
    assert (Basetype.equals s s2);
    Access.project_split x [x1; x2];
    split_entry y y1 y2;
    let d12 = Basetype.sumB [d1; d2] in
    begin
      let vm, vcdx = Builder.begin_block2 eval in
      let vs, vdx = Builder.unpair vcdx in
      let vd, vx = Builder.unpair vdx in
      let vd12 = Builder.project vd d12 in
      Builder.end_block_case vd12
        [ (fun vd1 -> eval1, [vm; Builder.pair vs (Builder.pair vd1 vx)]);
          (fun vd2 -> eval2, [vm; Builder.pair vs (Builder.pair vd2 vx)])
        ]
    end
  | Access.Base, _, _
  | Access.Pair _, _, _
  | Access.Fun _, _, _ ->
    assert false

let rec join_exit a1 a2 a : unit =
  match a, a1, a2 with
  | Access.Base, Access.Base, Access.Base -> ()
  | Access.Pair(m, x, y), Access.Pair(m1, x1, y1), Access.Pair(m2, x2, y2) ->
    assert (Basetype.equals m m1);
    assert (Basetype.equals m m2);
    join_exit x1 x2 x;
    join_exit y1 y2 y
  | Access.Fun(m, s, d, res, x, y),
    Access.Fun(m1, s1, d1, res1, x1, y1),
    Access.Fun(m2, s2, d2, res2, x2, y2) ->
    assert (Basetype.equals m m1);
    assert (Basetype.equals m m2);
    assert (Basetype.equals s s1);
    assert (Basetype.equals s s2);
    Access.join_embed [x1; x2] x;
    join_exit y1 y2 y;
    begin
      let arg = Builder.begin_block res1 in
      let vs, vres = Builder.unpair arg in
      let vy = join_code `Left vres y1 y2 y in
      Builder.end_block_jump res [Builder.pair vs vy]
    end;
    begin
      let arg = Builder.begin_block res2 in
      let vs, vres = Builder.unpair arg in
      let vy = join_code `Right vres y1 y2 y in
      Builder.end_block_jump res [Builder.pair vs vy]
    end
  | Access.Base, _, _
  | Access.Pair _, _, _
  | Access.Fun _, _, _ ->
    assert false

(* Annahme: alle blocks that jump to the defined blocks are defined already. *)
let rec build_blocks stage (t: term_with_interface) : unit =
  match t.desc with
  | Var x ->
    let arg = Builder.begin_block t.eval.entry in
    let va, vgamma = Builder.unpair arg in
    let vx = Context.build_lookup t.term.t_context x vgamma in
    let v = Builder.pair va vx in
    Builder.end_block_jump t.eval.exit [v]
  | Contr(((x, a), xs), s) ->
    let x_access = List.Assoc.find_exn t.context x in
    begin (* Eval block *)
      let arg = Builder.begin_block t.eval.entry in
      let vstack, vgamma = Builder.unpair arg in
      let vdelta =
        let delta = List.map s.term.t_context
            ~f:(fun (y, a) -> (if List.mem xs y then x else y), a) in
        Context.build_map t.term.t_context delta vgamma in
      let v = Builder.pair vstack vdelta in
      Builder.end_block_jump s.eval.entry [v]
    end;
    (* project blocks *)
    begin
      match xs with
      | [] -> (* variable unused; dummy block *)
        Access.unreachable x_access.exit
      | [y] -> (* singleton: no sum type *)
        let y_access = List.Assoc.find_exn s.context y in
        Access.forward x_access.exit y_access.exit
      | _ -> (* general case *)
        let xs_exits = List.map xs ~f:(fun x' -> (List.Assoc.find_exn s.context x').exit) in
        Access.project_split x_access.exit xs_exits
    end;
    (* body *)
    build_blocks stage s;
    (* eval exit *)
    let arg = Builder.begin_block s.eval.exit in
    Builder.end_block_jump t.eval.exit [arg];
    (* inject blocks *)
    begin
      match xs with
      | [] -> () (* no block needed *)
      | [y] -> (* singleton, no injection *)
        let y_access = List.Assoc.find_exn s.context y in
        Access.forward y_access.entry x_access.entry
      | _ ->
        let xs_entries = List.map xs ~f:(fun x' -> (List.Assoc.find_exn s.context x').entry) in
        Access.join_embed xs_entries x_access.entry
    end
  | Const(Ast.Cboolconst b, []) ->
    begin (* eval *)
      let arg = Builder.begin_block t.eval.entry in
      let vstack = Builder.fst arg in
      let v = Builder.pair vstack (Builder.boolconst b) in
      Builder.end_block_jump t.eval.exit [v]
    end
  | Const(Ast.Cintconst i, []) ->
    begin
      let arg = Builder.begin_block t.eval.entry in
      let vstack = Builder.fst arg in
      let vi = Builder.intconst i in
      let v = Builder.pair vstack vi in
      Builder.end_block_jump t.eval.exit [v]
    end
  | Const(Ast.Cintconst _, _) ->
    assert false
  | Const(Ast.Cintprint, [s]) ->
    begin (* eval entry *)
      let arg = Builder.begin_block t.eval.entry in
      Builder.end_block_jump s.eval.entry [arg]
    end;
    (* argument *)
    build_blocks stage s;
    begin (* print *)
      let arg = Builder.begin_block s.eval.exit in
      let vi = Builder.snd arg in
      ignore (Builder.primop (Ssa.Cintprint) vi);
      ignore (Builder.primop (Ssa.Cprint "\n") Builder.unit);
      Builder.end_block_jump t.eval.exit [arg]
    end
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
    begin (* eval1 *)
      let arg = Builder.begin_block t.eval.entry in
      let vstack, vgamma = Builder.unpair arg in
      let vgamma1 = Context.build_map t.term.t_context s1.term.t_context vgamma in
      let vgamma2 = Context.build_map t.term.t_context s2.term.t_context vgamma in
      let vstack1 = Builder.embed (Builder.pair vstack vgamma2) s1.term.t_ann in
      let v = Builder.pair vstack1 vgamma1 in
      Builder.end_block_jump s1.eval.entry [v]
    end;
    build_blocks stage s1;
    begin (* eval2 *)
      let arg = Builder.begin_block s1.eval.exit in
      let vstack1, vn1 = Builder.unpair arg in
      let vp = Builder.project vstack1
          (pairB t.term.t_ann (Context.code s2.term.t_context)) in
      let vstack, vgamma2 = Builder.unpair vp in
      let vstack2 = Builder.embed (Builder.pair vstack vn1) s2.term.t_ann in
      let v = Builder.pair vstack2 vgamma2 in
      Builder.end_block_jump s2.eval.entry [v]
    end;
    build_blocks stage s2;
    (* eval result *)
    begin
      let arg = Builder.begin_block s2.eval.exit in
      let vstack2, vn2 = Builder.unpair arg in
      let vp = Builder.project vstack2
                 (pairB t.term.t_ann (Cbvtype.code s1.term.t_type)) in
      let vstack, vn1 = Builder.unpair vp in
      let veq = Builder.primop primop (Builder.pair vn1 vn2) in
      let v = Builder.pair vstack veq in
      Builder.end_block_jump t.eval.exit [v]
    end
  | Const(_, _) ->
    assert false
  | Fun((x, xty), s) ->
    (* TODO: nimmt an, dass x im context von s vorkommt. *)
    let x_access = List.Assoc.find_exn s.context x in
    begin (* eval *)
      let arg = Builder.begin_block t.eval.entry in
      let vstack, vgamma = Builder.unpair arg in
      let vclosure = Builder.embed vgamma (Cbvtype.code t.term.t_type) in
      let v = Builder.pair vstack vclosure in
      Builder.end_block_jump t.eval.exit [v]
    end;
    begin (* access  *)
      match t.access.entry with
      | Access.Fun(_, _, _, eval, arg_exit, res_entry) ->
        begin
          let ve, vadx = Builder.begin_block2 eval in
          let va, vdx = Builder.unpair vadx in
          let vd, vx = Builder.unpair vdx in
          let vgamma = Builder.project vd (Context.code t.term.t_context) in
(*          let vgammax = Builder.pair vgamma vx in *)
          let vdelta =
            Context.encode ((x, vx) :: Context.decode vgamma t.term.t_context)
              s.term.t_context in
          (*
            Context.build_map ((x, xty)::t.term.t_context) s.term.t_context vgammax in
             *)
          (* TODO: Dokumentieren! *)
          let v = Builder.pair va vdelta in
          Builder.end_block_jump s.eval.entry [ve; v]
        end;
        (* TODO: forward kann man sich sparen? *)
        Access.forward res_entry s.access.entry;
        Access.forward arg_exit x_access.exit
      | _ -> assert false
    end;
    let gamma = List.filter s.context ~f:(fun (y, _) -> x <> y) in
    project_context t.context gamma;
    begin (* inner *)
      let inner_stage = Cbvtype.multiplicity t.term.t_type :: stage in
      build_blocks inner_stage s
    end;
    embed_context t.context gamma;
    begin (* access  *)
      match t.access.exit with
      | Access.Fun(_, _, _, res, arg_entry, res_exit) ->
        Access.forward s.access.exit res_exit;
        Access.forward x_access.entry arg_entry;
        begin (* s eval exit *)
          let ve, vv = Builder.begin_block2 s.eval.exit in
          Builder.end_block_jump res [ve; vv]
        end;
      | _ -> assert false
    end
  | Fix((th, f, x, xty), s) ->
    let x_access = List.Assoc.find_exn s.context x in
    let f_access = List.Assoc.find_exn s.context f in
    begin (* eval *)
      let arg = Builder.begin_block t.eval.entry in
      let vstack, vgamma = Builder.unpair arg in
      let vclosure = Builder.embed vgamma (Cbvtype.code t.term.t_type) in
      let v = Builder.pair vstack vclosure in
      Builder.end_block_jump t.eval.exit [v]
    end;
    (* E + H *G *)
    let tcons =
      let te = Cbvtype.multiplicity t.term.t_type in
      let tg = Cbvtype.multiplicity (List.Assoc.find_exn s.term.t_context f) in
      let thg = pairB th tg in
      Basetype.newty (Basetype.DataB(Basetype.Data.sumid 2, [te; thg])) in
    let build_singleton ve =
      Builder.embed (Builder.inj 0 ve tcons) th in
    let build_push vh vg =
      Builder.embed (Builder.inj 1 (Builder.pair vh vg) tcons) th in
    let stack_singleton src dst =
      Access.iter2_exn src dst
        ~f:(fun (ls, ms) (ld, _) ->
            let ds = List.length ms + 2 (* 2 to include E on stack! *)in
            match Builder.begin_blockn ds ls with
            | ve :: vv ->
              let vh = build_singleton ve in
              Builder.end_block_jump ld (vh :: vv)
            | _ -> assert false) in
    let stack_push src dst =
      Access.iter2_exn src dst
        ~f:(fun (ls, ms) (ld, _) ->
            let ds = List.length ms + 3 (* 3 to include H, E on stack! *) in
            match Builder.begin_blockn ds ls with
            | vh :: vg :: vv ->
              let vpushed = build_push vh vg in
              Builder.end_block_jump ld (vpushed :: vv)
            | _ -> assert false) in
    let stack_case src dst1 dst2 =
      Access.iter2_list_exn src [dst1; dst2]
        ~f:(fun (la, ma) ls ->
            match ls with
            | [(dst1, _); (dst2, _)] ->
              let da = List.length ma + 2 (* 2 to include H on stack!*) in
              begin
                match Builder.begin_blockn da la with
                | [] -> assert false
                | vh :: vv ->
                  let vcons = Builder.project vh tcons in
                  Builder.end_block_case vcons
                    [ (fun ve -> dst1, ve :: vv);
                      (fun vhg ->
                         let vh, vg = Builder.unpair vhg in
                         dst2, vh :: vg :: vv)
                    ]
              end
            | _ -> assert false) in
    (* eval *)
    let eval_body_block =
      let ts = s.term.t_ann in
      let td = Cbvtype.code t.term.t_type in
      let tx = Cbvtype.code xty in
      fresh_label stage "fix_eval_body" [th; pairB ts (pairB td tx)] in
    begin
      let vh, vadx = Builder.begin_block2 eval_body_block in
      let va, vdx = Builder.unpair vadx in
      let vd, vx = Builder.unpair vdx in
      let vgamma = Builder.project vd (Context.code t.term.t_context) in
      (*     let vgammadx = Builder.pair (Builder.pair vgamma vd) vx in *)
      let vdelta =
        Context.encode ((x, vx) :: (f, vd) :: Context.decode vgamma t.term.t_context)
          s.term.t_context in
      (*
      let vdelta = Context.build_map
                     ((x, xty) :: (f, t.term.t_type) :: t.term.t_context) s.term.t_context vgammadx in
         *)
      let v = (Builder.pair va vdelta) in
      Builder.end_block_jump s.eval.entry [vh; v]
    end;
    (* body *)
    build_blocks (th :: stage) s;
    (* access entry *)
    begin
      match t.access.entry with
      | Access.Fun(te, ts, td, eval, arg_exit, res_entry) ->
        begin
          let ve, vreq = Builder.begin_block2 eval in
          let vh = build_singleton ve in
          Builder.end_block_jump eval_body_block [vh; vreq]
        end;
        stack_singleton arg_exit x_access.exit;
        stack_singleton res_entry s.access.entry
      | _ ->
        assert false
    end;
    (* s eval exit *)
    begin
      match t.access.exit, f_access.exit with
      | Access.Fun(te, ts, td, res, arg_exit, res_entry),
        Access.Fun(tg, ts1, td1, rec_call, _, _) ->
        begin
          let vh, vm = Builder.begin_block2 s.eval.exit in
          let vcons = Builder.project vh tcons in
          Builder.end_block_case
            vcons
            [ (fun ve -> res, [ve; vm]);
              (fun vhg ->
                 let vh, vg = Builder.unpair vhg in
                 rec_call, [vh; vg; vm])
            ]
        end
      | _ ->
        assert false
    end;
    begin
      match t.access.entry, f_access.entry with
      | Access.Fun(te, ts, td, eval, arg_exit, res_entry),
        Access.Fun(tg, ts1, td1, rec_eval, rec_arg_exit, rec_res_entry) ->
        begin
          let vh, vg, vm = Builder.begin_block3 rec_eval in
          let vpushed = build_push vh vg in
          Builder.end_block_jump eval_body_block [vpushed; vm]
        end;
        stack_push rec_arg_exit x_access.exit;
        stack_push rec_res_entry s.access.entry
      | _ ->
        assert false
    end;

    begin
      match t.access.exit, f_access.exit with
      | Access.Fun(te, ts, td, res, arg_entry, res_exit),
        Access.Fun(tg, ts1, td1, rec_res, rec_arg_entry, rec_res_exit) ->
        stack_case x_access.entry arg_entry rec_arg_entry;
        stack_case s.access.exit res_exit rec_res_exit
      | _ ->
        assert false
    end;

    let gamma = List.Assoc.remove (List.Assoc.remove s.context x) f in
    project_context t.context gamma;
    embed_context t.context gamma;
  | Tailfix((th, f, x, xty), s) ->
    (* TODO: check order *)
    begin (* eval *)
      let arg = Builder.begin_block t.eval.entry in
      let vstack, vgamma = Builder.unpair arg in
      let vclosure = Builder.embed vgamma (Cbvtype.code t.term.t_type) in
      let v = Builder.pair vstack vclosure in
      Builder.end_block_jump t.eval.exit [v]
    end;
    begin
      match t.access.entry with
      | Access.Fun(te, ts, td, eval, a1, a2) ->
        begin (* eval_body *)
          let ve, vadx = Builder.begin_block2 ~may_append:false eval in
          let va, vdx = Builder.unpair vadx in
          let vd, vx = Builder.unpair vdx in
          let vgamma = Builder.project vd (Context.code t.term.t_context) in
          let vdelta =
            Context.encode ((x, vx) :: (f, vd) :: Context.decode vgamma t.term.t_context)
              s.term.t_context in
          (*
          let vgammadx = Builder.pair (Builder.pair vgamma vd) vx in
          let vdelta = Context.build_map
                         ((x, xty) :: (f, t.term.t_type) :: t.term.t_context) s.term.t_context vgammadx in
             *)
          let vh = Builder.embed (Builder.pair ve va) th in
          let vu = Builder.embed Builder.unit s.term.t_ann in
          let v = Builder.pair vu vdelta in
          Builder.end_block_jump s.eval.entry [vh; v]
        end;
      | _ ->
        assert false
    end;
    let gamma = List.filter s.context
                  ~f:(fun (y, _) -> y <> x && y <> f) in
    project_context t.context gamma;
    build_blocks (th :: stage) s;
    embed_context t.context gamma;
    begin
      match t.access.exit with
      | Access.Fun(te, ta, td, res, a1, a2) ->
        let x_access = List.Assoc.find_exn s.context x in
        Access.unreachable s.access.exit;
        Access.unreachable x_access.entry;
        begin (* s eval exit *)
          let vh, vum = Builder.begin_block2 s.eval.exit in
          let vm = Builder.snd vum in
          let vea = Builder.project vh (pairB te ta) in
          let ve, va = Builder.unpair vea in
          Builder.end_block_jump res [ve; Builder.pair va vm]
        end;
      | _ ->
        assert false
    end;
    let f_access = List.Assoc.find_exn s.context f in
    begin
      match t.access.entry, f_access.entry with
      | Access.Fun(te, ta, td, eval, a1, a2),
        Access.Fun(_, _, _, feval, b1, b2) ->
        begin (* f access entry *)
          let vh, vg, vm = Builder.begin_block3 feval in
          let vea = Builder.project vh (pairB te ta) in
          let ve, va = Builder.unpair vea in
          Builder.end_block_jump eval [ve; Builder.pair va (Builder.snd vm)]
        end
      | _ ->
        assert false
    end
  | Pair(t1, t2) ->
    begin (* eval *)
      let arg = Builder.begin_block t.eval.entry in
      let vu, vgammadelta = Builder.unpair arg in
      let vgamma = Context.build_map t.term.t_context t1.term.t_context vgammadelta in
      let vdelta = Context.build_map t.term.t_context t2.term.t_context vgammadelta in
      let embed_val = Builder.embed (Builder.pair vu vdelta) t1.term.t_ann in
      let v = Builder.pair embed_val vgamma in
      Builder.end_block_jump t1.eval.entry [v]
    end;
    (* access entry *)
    begin
      match t.access.entry with
      | Access.Pair(_, a1, a2) ->
        Access.pop_embed a1 t1.access.entry;
        Access.pop_embed a2 t2.access.entry
      | _ ->
        assert false
    end;
    build_blocks stage t1;
    build_blocks stage t2;
    begin (* block 2 *)
      let arg = Builder.begin_block t1.eval.exit in
      let ve, vf = Builder.unpair arg in
      let vu_delta = Builder.project ve
          (pairB t.term.t_ann (Context.code t2.term.t_context)) in
      let vu, vdelta = Builder.unpair vu_delta in
      let vu_f = Builder.pair vu vf in
      let ve' = Builder.embed vu_f t2.term.t_ann in
      let v = Builder.pair ve' vdelta in
      Builder.end_block_jump t2.eval.entry [v]
    end;
    begin (* block 3*)
      let arg = Builder.begin_block t2.eval.exit in
      let ve, v2 = Builder.unpair arg in
      let vu_f = Builder.project ve (pairB t.term.t_ann (Cbvtype.code t1.term.t_type)) in
      let vu, v1 = Builder.unpair vu_f in
      let v = Builder.pair vu (Builder.pair v1 v2) in
      Builder.end_block_jump t.eval.exit [v]
    end;
    (* access exit *)
    begin
      match t.access.exit with
      | Access.Pair(_, a1, a2) ->
        Access.project_push t1.access.exit a1;
        Access.project_push t2.access.exit a2
      | _ ->
        assert false
    end
  | Fst(t1) ->
    begin (* eval entry *)
      let arg = Builder.begin_block t.eval.entry in
      Builder.end_block_jump t1.eval.entry [arg]
    end;
    (* access entry *)
    begin
      match t1.access.entry with
      | Access.Pair(_, a1, a2) ->
        (* push multiplicity of pair type *)
        Access.push_unit_embed t.access.entry a1
      | _ ->
        assert false
    end;
    (* Body *)
    build_blocks stage t1;
    begin (* eval exit *)
      let arg = Builder.begin_block t1.eval.exit in
      let vm, vp = Builder.unpair arg in
      let vp1 = Builder.fst vp in
      let v = Builder.pair vm vp1 in
      Builder.end_block_jump t.eval.exit [v]
    end;
    (* access exit *)
    begin
      match t1.access.exit with
      | Access.Pair(_, a1, a2) ->
        (* discard multiplicity of pair type *)
        Access.pop_discard a1 t.access.exit;
        Access.unreachable a2
      | _ ->
        assert false
    end
  | Snd(t1) ->
    begin (* eval entry *)
      let arg = Builder.begin_block t.eval.entry in
      Builder.end_block_jump t1.eval.entry [arg]
    end;
    begin
      match t1.access.entry with
      | Access.Pair(_, a1, a2) ->
        (* push multiplicity of pair type *)
        Access.push_unit_embed t.access.entry a2
      | _ ->
        assert false
    end;
    (* body *)
    build_blocks stage t1;
    begin (* eval exit *)
      let arg = Builder.begin_block t1.eval.exit in
      let vm, vp = Builder.unpair arg in
      let vp2 = Builder.snd vp in
      let v = Builder.pair vm vp2 in
      Builder.end_block_jump t.eval.exit [v]
    end;
    (* access exit *)
    begin
      match t1.access.exit with
      | Access.Pair(_, a1, a2) ->
        (* discard multiplicity of pair type *)
        Access.pop_discard a2 t.access.exit;
        Access.unreachable a1
      | _ ->
        assert false
    end
  | App(t1, t2) ->
    (* TODO: order isn't right *)
    begin (* eval *)
      let arg = Builder.begin_block t.eval.entry in
      let vu, vgammadelta = Builder.unpair arg in
      let vgamma = Context.build_map t.term.t_context t1.term.t_context vgammadelta in
      let vdelta = Context.build_map t.term.t_context t2.term.t_context vgammadelta in
      let embed_val = Builder.embed (Builder.pair vu vdelta) t1.term.t_ann in
      let v = Builder.pair embed_val vgamma in
      Builder.end_block_jump t1.eval.entry [v]
    end;
    (* TODO: wäre besser, wenn der eval-Block von t2 hier schon konstruiert waere *)
    build_blocks stage t1;
    begin (* block 2 *)
      let arg = Builder.begin_block t1.eval.exit in
      let ve, vf = Builder.unpair arg in
      let vu_delta = Builder.project ve
          (pairB t.term.t_ann (Context.code t2.term.t_context)) in
      let vu, vdelta = Builder.unpair vu_delta in
      let vu_f = Builder.pair vu vf in
      let ve' = Builder.embed vu_f t2.term.t_ann in
      let v = Builder.pair ve' vdelta in
      Builder.end_block_jump t2.eval.entry [v]
    end;
    begin
      match t1.access.exit with
      | Access.Fun(_, _, _, res1, x_entry, y_exit) ->
        Access.pop_discard y_exit t.access.exit;
        Access.pop_discard x_entry t2.access.entry;
        begin (* block 8 *)
          let arg = Builder.begin_block res1 in
          let vv, vres = Builder.unpair arg in
          let vu = Builder.project vv t.term.t_ann in
          let v = Builder.pair vu vres in
          Builder.end_block_jump t.eval.exit [v]
        end
      | _ ->
        assert false
    end;
    build_blocks stage t2;
    begin
      match t1.access.entry with
      | Access.Fun(td, ts, _, apply, x_exit, y_entry) ->
        begin (* block 3 *)
          let arg = Builder.begin_block t2.eval.exit in
          let ve, vx = Builder.unpair arg in
          let vu_f = Builder.project ve (pairB t.term.t_ann (Cbvtype.code t1.term.t_type)) in
          let vu, vf = Builder.unpair vu_f in
          let vs = Builder.embed vu ts in
          let vsfx = Builder.pair vs (Builder.pair vf vx) in
          let vd = Builder.embed Builder.unit td in
          Builder.end_block_jump apply [vd; vsfx]
        end;
        Access.push_unit_embed t.access.entry y_entry;
        Access.push_unit_embed t2.access.exit x_exit
      | _ ->
        assert false
    end
  | Ifz(tc, t1, t2) ->
    begin (* eval 1 *)
      let arg = Builder.begin_block t.eval.entry in
      let vstack, vgamma = Builder.unpair arg in
      let vgammac = Context.build_map t.term.t_context tc.term.t_context vgamma in
      let vgamma1 = Context.build_map t.term.t_context t1.term.t_context vgamma in
      let vgamma2 = Context.build_map t.term.t_context t2.term.t_context vgamma in
      let vstack1 = Builder.embed (Builder.pair vstack (Builder.pair vgamma1 vgamma2)) tc.term.t_ann in
      let v = Builder.pair vstack1 vgammac in
      Builder.end_block_jump tc.eval.entry [v]
    end;
    build_blocks stage tc;
    begin (* eval c *)
      let arg = Builder.begin_block tc.eval.exit in
      let vstack1, vz = Builder.unpair arg in
      let vp = Builder.project vstack1 (pairB t.term.t_ann
                                          (pairB
                                             (Context.code t1.term.t_context)
                                             (Context.code t2.term.t_context)
                                          )) in
      let vstack, vgamma12 = Builder.unpair vp in
      let vgamma1, vgamma2 = Builder.unpair vgamma12 in
      Builder.end_block_case vz
        [ (fun _ -> t1.eval.entry, [Builder.pair vstack vgamma1]);
          (fun _ -> t2.eval.entry, [Builder.pair vstack vgamma2]) ]
    end;
    split_entry t.access.entry t1.access.entry t2.access.entry;
    build_blocks stage t1;
    build_blocks stage t2;
    begin (* eval rt *)
      let arg = Builder.begin_block t1.eval.exit in
      let vstack = Builder.fst arg in
      let vn = Builder.snd arg in
      let v = Builder.pair vstack (join_code `Left vn t1.access.entry t2.access.entry t.access.entry) in
      Builder.end_block_jump t.eval.exit [v]
    end;
    begin (* eval rf *)
      let arg = Builder.begin_block t2.eval.exit in
      let vstack = Builder.fst arg in
      let vn = Builder.snd arg in
      let v = Builder.pair vstack (join_code `Right vn t1.access.entry t2.access.entry t.access.entry) in
      Builder.end_block_jump t.eval.exit [v]
    end;
    (* access c *)
    Access.unreachable tc.access.exit;
    join_exit t1.access.exit t2.access.exit t.access.exit

let to_ssa t =
  Builder.reset();
  let stage = [] in
  let f = add_interface stage t in
  build_blocks stage f;
  let ret_ty = List.hd_exn f.eval.exit.Ssa.arg_types in
  (* return *)
  let arg = Builder.begin_block f.eval.exit in
  Builder.end_block_return arg;
  (* access exit *)
  Access.unreachable f.access.exit;
  let visited = Ident.Table.create () in
  let rev_sorted_blocks = ref [] in
  let rec sort_blocks i =
    if not (Ident.Table.mem visited i) then
      begin
        (*        Printf.printf "%s\n%!" (Ident.to_string i);*)
        Ident.Table.set visited ~key:i ~data:();

        let b = Ident.Table.find_exn Builder.blocks i in
        (*        Ssa.fprint_block stdout b;*)
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
