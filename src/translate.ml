open Core_kernel.Std
open Cbvterm

module Builder = Ssabuilder

type stage = Basetype.t list

let fresh_label (ms: stage) (name: string) (loc) (a : Basetype.t): Ssa.label =
  { Ssa.name = Ident.fresh name;
    Ssa.arg_types = a :: ms;
    Ssa.debug_loc = loc
  }

(* type of the n-th stage:
   0 = type of message,
   1 = type of first stage,
   ... *)
let type_of_stage l n =
  List.nth_exn l.Ssa.arg_types n

let focus (n: int) (args: Builder.value list) =
  let h, t = List.split_n args n in
  List.rev h, t

let unfocus h t =
  List.rev h @ t

(** Representation and manipulation of interfaces to access encoded values. *)
module Access : sig
  type t =
      Base
    | Tuple of t list
    | Fun of Basetype.t * Ssa.label * t * t

  val iter2_exn: t -> t ->
    f:((Ssa.label * int) -> (Ssa.label * int) -> unit) ->
    unit

  val iter2_list_exn: t -> t list ->
    f:((Ssa.label * int) -> (Ssa.label * int) list -> unit) ->
    unit

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
    | Tuple of t list
    | Fun of Basetype.t * Ssa.label * t * t

  (* TODO: document label arguments *)
  let labels (a: t) : (Ssa.label * int) list =
    let rec ls (a: t) (ds: int) : (Ssa.label * int) list =
      match a with
      | Base -> []
      | Tuple(xs) ->
        List.concat_map xs ~f:(fun x -> ls x (ds + 1))
      | Fun(_, app, x, y) ->
        let ds' = ds + 1 in
        (app, ds' + 1) :: (ls x ds') @ (ls y ds') in
    ls a 0

  let iter a = List.iter (labels a)

  let iter2_exn a b ~f:f  =
    List.iter2_exn (labels a) (labels b) ~f:f

  let iter2_list_exn a xs ~f:f  =
    let ls = List.map ~f:labels xs |> List.transpose_exn in
    List.iter2_exn (labels a) ls ~f:f

  let forward a b : unit =
    iter2_exn a b
      ~f:(fun (la, _) (lb, _) ->
          let args = Builder.begin_block la in
          Builder.end_block_jump lb args)

  let unreachable a : unit =
    iter a
      ~f:(fun (l, _) ->
        ignore (Builder.begin_block1 l);
        Builder.end_block_unreachable ())

  (* Gamma |- C.X to Gamma |- A1.X, ..., Gamma |- An.X where A1*...*An <= C *)
  let project_split a al : unit =
    iter2_list_exn a al
      ~f:(fun (la, da) ls ->
        let dsts, mults = List.unzip ls in
        let outermults = List.map ls ~f:(fun (l, d) -> type_of_stage l d) in
        let tsum = Basetype.sumB outermults in
        let va, args = focus (da + 1) (Builder.begin_block la) in
        match va with
        | [] -> assert false
        | vm :: vv ->
          let vm' = Builder.project vm tsum in
          let cases = List.map dsts ~f:(fun dst ->
            fun c -> dst, unfocus (c :: vv) args) in
          Builder.end_block_case vm' cases
      )

  (* Gamma |- A1.X, ..., Gamma |- An.X to Gamma |- C.X where A1*...*An <= C *)
  let join_embed al a : unit =
    iter2_list_exn a al
      ~f:(fun (dst, dst_mults) ls ->
        let outermults = List.map ls ~f:(fun (l, d) -> type_of_stage l d) in
        let tsum = Basetype.sumB outermults in
        let dst_outermult = type_of_stage dst (dst_mults) in
        List.iteri ls
          ~f:(fun i (src, src_mults) ->
            let n = src_mults + 1 in
            let va, args = focus n (Builder.begin_block src) in
            match va with
            | vm :: vv ->
              let vi = Builder.inj i vm tsum in
              let vm' = Builder.embed vi dst_outermult in
              Builder.end_block_jump dst (unfocus (vm' :: vv) args)
            | _ -> assert false
          )
      )

  (* Gamma |- C.X to Gamma, A |- B.X where A*B <= C *)
  let project_push a b : unit =
    iter2_exn a b
      ~f:(fun (la, da) (lb, db) ->
        let tb = type_of_stage lb db in
        let ww, args = focus (da + 1) (Builder.begin_block la) in
        match ww with
        | vc :: vv ->
          (* ta is the first type in the context *)
          let ta = type_of_stage lb (db + 1) in
          let vm' = Builder.project vc (Basetype.pairB ta tb) in
          let va, vb = Builder.unpair vm' in
          Builder.end_block_jump lb (unfocus (va :: vb :: vv) args)
        | _ -> assert false
      )

  (* Gamma, A |- B.X to Gamma |- C.X where A*B <= C *)
  let pop_embed a b : unit =
    iter2_exn a b
      ~f:(fun (la, da) (lb, db) ->
        let tc = type_of_stage lb db in
        let ww, args = focus (da + 2) (Builder.begin_block la) in
        match ww with
        | va :: vb :: vv ->
          let vc = Builder.embed (Builder.pair va vb) tc in
          Builder.end_block_jump lb (unfocus (vc :: vv) args)
        | _ -> assert false
      )

  (* Gamma, C |- A.X to Gamma |- A.X where unit <= C *)
  let pop_discard a b : unit =
    iter2_exn a b
      ~f:(fun (la, da) (lb, _) ->
          let ww, args = focus (da + 2) (Builder.begin_block la) in
          match ww with
          | _ :: vv ->
            Builder.end_block_jump lb (unfocus vv args)
          | _ -> assert false
        )

  (* Gamma |- A.X to Gamma, C |- A.X where unit <= C *)
  let push_unit_embed a b : unit =
    iter2_exn a b
      ~f:(fun (la, da) (lb, db) ->
          let vv, args = focus (da + 1) (Builder.begin_block la) in
          let tc = type_of_stage lb (db + 1) in
          let vc = Builder.embed Builder.unit tc in
          Builder.end_block_jump lb (unfocus (vc :: vv) args)
        )

  let rec fresh_entry (ms: stage) (n: string) (a: Cbvtype.t): t =
    match Cbvtype.case a with
    | Cbvtype.Var -> failwith "var"
    | Cbvtype.Sgn s ->
      match s with
      | Cbvtype.Bool(m) -> Base
      | Cbvtype.Nat(m) -> Base
      | Cbvtype.Pair(m, (x, y)) ->
        let xentry = fresh_entry (m :: ms) n x in
        let yentry = fresh_entry (m :: ms) n y in
        Tuple([xentry; yentry])
      | Cbvtype.Fun(m, (x, s, c, y)) ->
        let xc = Cbvtype.code x in
        let yentry = fresh_entry (m :: ms) n y in
        let xexit = fresh_exit (m :: ms) n x in
        let eval = fresh_label (s :: m :: ms) (n ^ "_access_entry") None
                     (Basetype.pairB c xc) in
        Fun(c, eval, xexit, yentry)
  and fresh_exit (ms: stage) (n: string) (a: Cbvtype.t): t =
    match Cbvtype.case a with
    | Cbvtype.Var -> failwith "var"
    | Cbvtype.Sgn s ->
      match s with
      | Cbvtype.Bool(m) -> Base
      | Cbvtype.Nat(m) -> Base
      | Cbvtype.Pair(m, (x, y)) ->
        let xexit = fresh_exit (m :: ms) n x in
        let yexit = fresh_exit (m :: ms) n y in
        Tuple([xexit; yexit])
      | Cbvtype.Fun(m, (x, s, c, y)) ->
        let yc = Cbvtype.code y in
        let yexit = fresh_exit (m :: ms) n y in
        let xentry = fresh_entry (m :: ms) n x in
        let ret = fresh_label (s :: m :: ms) (n ^ "_access_exit") None yc in
        Fun(c, ret, xentry, yexit)
end

module Context : sig

  type t = Cbvtype.t Typing.context

  val code: t -> Basetype.t
  val decode: t -> Builder.value -> Builder.value Typing.context
  val encode: t -> Builder.value Typing.context -> Builder.value
  val build_map: t -> t -> Builder.value -> Builder.value

end =
struct

  type t = Cbvtype.t Typing.context

  let code (gamma : t) : Basetype.t =
    Typing.code_of_context gamma

  let decode (gamma : t) (v: Builder.value) : (Builder.value Typing.context) =
    assert (Basetype.equals (Builder.typeof v) (code gamma));
    List.mapi gamma ~f:(fun i (x, _) -> x, Builder.proj v i)

  let encode (gamma : t) (vs: Builder.value Typing.context) : Builder.value =
    let vs =
      List.map gamma ~f:(fun (x, a) ->
          let vx = List.Assoc.find_exn vs x in
          assert (Basetype.equals (Builder.typeof vx) (Cbvtype.code a));
          vx) in
    Builder.tuple vs

  let build_map (gamma: t) (delta: t) (vgamma: Builder.value) : Builder.value =
    let vs = decode gamma vgamma in
    encode delta vs
end

type 'a interface = {
  entry: 'a;
  exit: 'a
}

type eval_interface = Ssa.label interface
type access_interface = Access.t interface

type term_with_interface = {
  desc: (term_with_interface, Cbvtype.t) Cbvterm.sgn;
  eval: eval_interface;
  access: access_interface;
  context: access_interface Typing.context;
  term: Cbvterm.t;
}

let block_name_of_term (t: Cbvterm.t) : string =
  let open Ast.Location in
  match t.t_loc with
  | Some l ->
    Printf.sprintf "_l%i_c%i" l.start_pos.line l.start_pos.column
  | None -> ""

let fresh_eval (ms: stage) (t: Cbvterm.t) : eval_interface =
  let s = block_name_of_term t in
  { entry = fresh_label (t.t_ann :: ms) (s ^ "_eval_entry") t.t_loc
              (Context.code t.t_context);
    exit  = fresh_label (t.t_ann :: ms) (s ^ "_eval_exit") t.t_loc
              (Cbvtype.code t.t_type) }

let fresh_access_named (ms: stage) (n : string) (a : Cbvtype.t)
  : access_interface =
  { entry = Access.fresh_entry ms n a;
    exit = Access.fresh_exit ms n a }

let fresh_access (ms: stage) (t: Cbvterm.t) : access_interface =
  let n = block_name_of_term t in
  fresh_access_named ms n t.t_type

let rec add_interface (ms : stage) (t : Cbvterm.t) : term_with_interface =
  let context_interface =
    List.map ~f:(fun (y, a) -> (y, fresh_access_named ms "context" a)) in
  match t.t_desc with
  | Var x ->
    let eval = fresh_eval ms t in
    let access = fresh_access ms t in
    { desc = Var x;
      eval = eval;
      access = access;
      context = [(x, access)];
      term = t
    }
  | Contr(((x, a), xs), s) ->
    let si = add_interface ms s in
    let eval = fresh_eval ms t in
    let x_access = fresh_access_named ms "contr" a in
    { desc = Contr(((x, a), xs), si);
      eval = eval;
      access = si.access;
      context = (x, x_access) ::
                (List.filter si.context
                   ~f:(fun (x, _) -> not (List.mem xs x)));
      term = t
    }
  | Const(Ast.Cboolconst b, []) ->
    let eval = fresh_eval ms t in
    let access = fresh_access ms t in
    { desc = Const(Ast.Cboolconst b, []);
      eval = eval;
      access = access;
      context = [];
      term = t
    }
  | Const(Ast.Cintconst i, []) ->
    let eval = fresh_eval ms t in
    let access = fresh_access ms t in
    { desc = Const(Ast.Cintconst i, []);
      eval = eval;
      access = access;
      context = [];
      term = t
    }
  | Const(Ast.Cintconst _, _) ->
    assert false
  | Const(Ast.Cprint(s), []) ->
    let eval = fresh_eval ms t in
    let access = fresh_access ms t in
    { desc = Const(Ast.Cprint(s), []);
      eval = eval;
      access = access;
      context = [];
      term = t
    }
  | Const(Ast.Cprint _, _) ->
    assert false
  | Const(Ast.Cintprint, [s]) ->
    let si = add_interface ms s in
    let eval = fresh_eval ms t in
    let access = fresh_access ms t in
    { desc = Const(Ast.Cintprint, [si]);
      eval = eval;
      access = access;
      context = si.context;
      term = t
    }
  | Const(Ast.Cintprint, _) ->
    assert false
  | Const(c, [s1; s2]) ->
    let s1i = add_interface ms s1 in
    let s2i = add_interface ms s2 in
    let eval = fresh_eval ms t in
    let access = fresh_access ms t in
    { desc = Const(c, [s1i; s2i]);
      eval = eval;
      access = access;
      context = s1i.context @ s2i.context;
      term = t;
    }
  | Const(_, _) ->
    assert false
  | Fun((x, xty), s) ->
    let inner_ms = Cbvtype.multiplicity t.t_type :: ms in
    let si = add_interface inner_ms s in
    let eval = fresh_eval ms t in
    let access = fresh_access ms t in
    let context = context_interface t.t_context in
    { desc = Fun((x, xty), si);
      eval = eval;
      access = access;
      context = context;
      term = t
    }
  | Fix((th, f, x, xty), s) ->
    let si = add_interface (th :: ms) s in
    let eval = fresh_eval ms t in
    let access = fresh_access ms t in
    let context = context_interface t.t_context in
    { desc = Fix((th, f, x, xty), si);
      eval = eval;
      access = access;
      context = context;
      term = t
    }
  | Tailfix((th, f, x, xty), s) ->
    let si = add_interface (th :: ms) s in
    let eval = fresh_eval ms t in
    let access = fresh_access ms t in
    let context = context_interface t.t_context in
    { desc = Tailfix((th, f, x, xty), si);
      eval = eval;
      access = access;
      context = context;
      term = t
    }
  | Pair(t1, t2) ->
    let t1i = add_interface ms t1 in
    let t2i = add_interface ms t2 in
    let eval = fresh_eval ms t in
    let access = fresh_access ms t in
    { desc = Pair(t1i, t2i);
      eval = eval;
      access = access;
      context = t1i.context @ t2i.context;
      term = t
    }
  | Proj(t1, i) ->
    let t1i = add_interface ms t1 in
    let eval = fresh_eval ms t in
    let access = fresh_access ms t in
    { desc = Proj(t1i, i);
      eval = eval;
      access = access;
      context = t1i.context;
      term = t
    }
  | App(t1, t2) ->
    let t1i = add_interface ms t1 in
    let t2i = add_interface ms t2 in
    let eval = fresh_eval ms t in
    let access = fresh_access ms t in
    { desc = App(t1i, t2i);
      eval = eval;
      access = access;
      context = t1i.context @ t2i.context;
      term = t
    }
  | If(tc, t1, t2) ->
    let tci = add_interface ms tc in
    let t1i = add_interface ms t1 in
    let t2i = add_interface ms t2 in
    let eval = fresh_eval ms t in
    let access = fresh_access_named ms "join" t.t_type in
    { desc = If(tci, t1i, t2i);
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

let rec join_code (k: [> `Left | `Right]) (v: Builder.value)
          (a1: Access.t) (a2: Access.t) (a: Access.t) : Builder.value =
  let i = match k with
    | `Left -> 0
    | `Right -> 1 in
  match a, a1, a2 with
  | Access.Base, Access.Base, Access.Base -> v
  | Access.Tuple(xs), Access.Tuple(xs1), Access.Tuple(xs2) ->
    let vv = Builder.untuple v in
    let rec join vv xs1 xs2 xs =
      match vv, xs1, xs2, xs with
      | [], [], [], [] -> []
      | v :: vv, x1 :: xs1, x2 :: xs2, x :: xs ->
        let v' = join_code k v x1 x2 x in
        v' :: join vv xs1 xs2 xs
      | _ -> assert false in
    let vv' = join vv xs1 xs2 xs in
    Builder.tuple vv'
  | Access.Fun(d, _, _, _),
    Access.Fun(d1, _, _, _),
    Access.Fun(d2, _, _, _) ->
    let vi = Builder.inj i v (Basetype.sumB [d1; d2]) in
    Builder.embed vi d
  | Access.Base, _, _
  | Access.Tuple _, _, _
  | Access.Fun _, _, _ ->
    assert false

let rec split_entry (a: Access.t) (a1: Access.t) (a2: Access.t) : unit =
  match a, a1, a2 with
  | Access.Base, Access.Base, Access.Base -> ()
  | Access.Tuple(xs), Access.Tuple(xs1), Access.Tuple(xs2) ->
    let rec split xs xs1 xs2 =
      match xs, xs1, xs2 with
      | [], [], [] -> ()
      | x :: xs, x1 :: xs1, x2 :: xs2 ->
        split_entry x x1 x2;
        split xs xs1 xs2
      | _ -> assert false in
    split xs xs1 xs2
  | Access.Fun(_, eval, x, y),
    Access.Fun(d1, eval1, x1, y1),
    Access.Fun(d2, eval2, x2, y2) ->
    Access.project_split x [x1; x2];
    split_entry y y1 y2;
    let d12 = Basetype.sumB [d1; d2] in
    begin
      let vdx, vs, args = Builder.begin_block2 eval in
      let vd, vx = Builder.unpair vdx in
      let vd12 = Builder.project vd d12 in
      Builder.end_block_case vd12
        [ (fun vd1 -> eval1, Builder.pair vd1 vx :: vs :: args);
          (fun vd2 -> eval2, Builder.pair vd2 vx :: vs :: args)
        ]
    end
  | Access.Base, _, _
  | Access.Tuple _, _, _
  | Access.Fun _, _, _ ->
    assert false

let rec join_exit (a1: Access.t) (a2: Access.t) (a: Access.t) : unit =
  match a, a1, a2 with
  | Access.Base, Access.Base, Access.Base -> ()
  | Access.Tuple(xs), Access.Tuple(xs1), Access.Tuple(xs2) ->
    let rec join xs1 xs2 xs =
      match xs1, xs2, xs with
      | [], [], [] -> ()
      | x1 :: xs1, x2 :: xs2, x :: xs ->
        join_exit x1 x2 x;
        join xs1 xs2 xs
      | _ -> assert false in
    join xs1 xs2 xs
  | Access.Fun(_, res, x, y),
    Access.Fun(_, res1, x1, y1),
    Access.Fun(_, res2, x2, y2) ->
    Access.join_embed [x1; x2] x;
    join_exit y1 y2 y;
    begin
      let vres, vs, args = Builder.begin_block2 res1 in
      let vy = join_code `Left vres y1 y2 y in
      Builder.end_block_jump res (vy :: vs :: args)
    end;
    begin
      let vres, vs, args = Builder.begin_block2 res2 in
      let vy = join_code `Right vres y1 y2 y in
      Builder.end_block_jump res (vy :: vs :: args)
    end
  | Access.Base, _, _
  | Access.Tuple _, _, _
  | Access.Fun _, _, _ ->
    assert false

(* Annahme: alle blocks that jump to the defined blocks are defined already. *)
let rec build_blocks (ms: stage) (t: term_with_interface) : unit =
  match t.desc with
  | Var x ->
    let vgamma, va, args = Builder.begin_block2 t.eval.entry in
    let vx = List.Assoc.find_exn (Context.decode t.term.t_context vgamma) x in
    Builder.end_block_jump t.eval.exit (vx :: va :: args)
  | Contr(((x, a), xs), s) ->
    let x_access = List.Assoc.find_exn t.context x in
    begin (* Eval block *)
      let vgamma, vstack, args = Builder.begin_block2 t.eval.entry in
      let vdelta =
        let delta = List.map s.term.t_context
            ~f:(fun (y, a) -> (if List.mem xs y then x else y), a) in
        Context.build_map t.term.t_context delta vgamma in
      Builder.end_block_jump s.eval.entry (vdelta :: vstack :: args)
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
        let xs_exits =
          List.map xs ~f:(fun x' -> (List.Assoc.find_exn s.context x').exit) in
        Access.project_split x_access.exit xs_exits
    end;
    (* body *)
    build_blocks ms s;
    (* eval exit *)
    let args = Builder.begin_block s.eval.exit in
    Builder.end_block_jump t.eval.exit args;
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
      let _, vstack, args = Builder.begin_block2 t.eval.entry in
      Builder.end_block_jump t.eval.exit (Builder.boolconst b :: vstack :: args)
    end
  | Const(Ast.Cintconst i, []) ->
    begin
      let _, vstack, args = Builder.begin_block2 t.eval.entry in
      let vi = Builder.intconst i in
      Builder.end_block_jump t.eval.exit (vi :: vstack :: args)
    end
  | Const(Ast.Cintconst _, _) ->
    assert false
  | Const(Ast.Cprint s, _) ->
    begin (* print *)
      let vi, vstack, args = Builder.begin_block2 t.eval.entry in
      ignore (Builder.primop (Ssa.Cprint s) Builder.unit);
      Builder.end_block_jump t.eval.exit (Builder.intconst 0 :: vstack :: args)
    end
  | Const(Ast.Cintprint, [s]) ->
    begin (* eval entry *)
      let args = Builder.begin_block t.eval.entry in
      Builder.end_block_jump s.eval.entry args
    end;
    (* argument *)
    build_blocks ms s;
    begin (* print *)
      let vi, vstack, args = Builder.begin_block2 s.eval.exit in
      ignore (Builder.primop (Ssa.Cintprint) vi);
      Builder.end_block_jump t.eval.exit (vi :: vstack :: args)
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
      | Ast.Cprint _ -> assert false
      | Ast.Cboolconst _ -> assert false
      | Ast.Cintconst _ -> assert false
      | Ast.Cintprint -> assert false in
    begin (* eval1 *)
      let vgamma, vstack, args = Builder.begin_block2 t.eval.entry in
      let vgamma1 = Context.build_map t.term.t_context s1.term.t_context vgamma in
      let vgamma2 = Context.build_map t.term.t_context s2.term.t_context vgamma in
      let vstack1 = Builder.embed (Builder.pair vstack vgamma2) s1.term.t_ann in
      Builder.end_block_jump s1.eval.entry (vgamma1 :: vstack1 :: args)
    end;
    build_blocks ms s1;
    begin (* eval2 *)
      let vn1, vstack1, args = Builder.begin_block2 s1.eval.exit in
      let vp = Builder.project vstack1
          (Basetype.pairB t.term.t_ann (Context.code s2.term.t_context)) in
      let vstack, vgamma2 = Builder.unpair vp in
      let vstack2 = Builder.embed (Builder.pair vstack vn1) s2.term.t_ann in
      Builder.end_block_jump s2.eval.entry (vgamma2 :: vstack2 :: args)
    end;
    build_blocks ms s2;
    (* eval result *)
    begin
      let vn2, vstack2, args = Builder.begin_block2 s2.eval.exit in
      let vp = Builder.project vstack2
                 (Basetype.pairB t.term.t_ann (Cbvtype.code s1.term.t_type)) in
      let vstack, vn1 = Builder.unpair vp in
      let veq = Builder.primop primop (Builder.pair vn1 vn2) in
      Builder.end_block_jump t.eval.exit (veq :: vstack :: args)
    end
  | Const(_, _) ->
    assert false
  | Fun((x, xty), s) ->
    (* TODO: nimmt an, dass x im context von s vorkommt. *)
    let x_access = List.Assoc.find_exn s.context x in
    begin (* eval *)
      let vgamma, vstack, args = Builder.begin_block2 t.eval.entry in
      let vclosure = Builder.embed vgamma (Cbvtype.code t.term.t_type) in
      Builder.end_block_jump t.eval.exit (vclosure :: vstack :: args)
    end;
    begin (* access  *)
      match t.access.entry with
      | Access.Fun(_, eval, arg_exit, res_entry) ->
        begin
          let vdx, va, ve, args = Builder.begin_block3 eval in
          let vd, vx = Builder.unpair vdx in
          let vgamma = Builder.project vd (Context.code t.term.t_context) in
          let vdelta =
            Context.encode s.term.t_context
              ((x, vx) :: Context.decode t.term.t_context vgamma) in
          Builder.end_block_jump s.eval.entry (vdelta :: va :: ve :: args)
        end;
        (* TODO: forward kann man sich sparen? *)
        Access.forward res_entry s.access.entry;
        Access.forward arg_exit x_access.exit
      | _ -> assert false
    end;
    let gamma = List.filter s.context ~f:(fun (y, _) -> x <> y) in
    project_context t.context gamma;
    begin (* inner *)
      let inner_ms = Cbvtype.multiplicity t.term.t_type :: ms in
      build_blocks inner_ms s
    end;
    embed_context t.context gamma;
    begin (* access  *)
      match t.access.exit with
      | Access.Fun(_, res, arg_entry, res_exit) ->
        Access.forward s.access.exit res_exit;
        Access.forward x_access.entry arg_entry;
        begin (* s eval exit *)
          let vr, va, ve, args = Builder.begin_block3 s.eval.exit in
          Builder.end_block_jump res (vr :: va :: ve :: args)
        end;
      | _ -> assert false
    end
  | App(t1, t2) ->
    begin (* eval *)
      let vgammadelta, vu, args = Builder.begin_block2 t.eval.entry in
      let vgamma = Context.build_map t.term.t_context t1.term.t_context vgammadelta in
      let vdelta = Context.build_map t.term.t_context t2.term.t_context vgammadelta in
      let embed_val = Builder.embed (Builder.pair vu vdelta) t1.term.t_ann in
      Builder.end_block_jump t1.eval.entry (vgamma :: embed_val :: args)
    end;
    (* TODO: wäre besser, wenn der eval-Block von t2 hier schon konstruiert waere *)
    build_blocks ms t1;
    begin (* block 2 *)
      let vf, ve, args = Builder.begin_block2 t1.eval.exit in
      let vu_delta = Builder.project ve
          (Basetype.pairB t.term.t_ann (Context.code t2.term.t_context)) in
      let vu, vdelta = Builder.unpair vu_delta in
      let vu_f = Builder.pair vu vf in
      let ve' = Builder.embed vu_f t2.term.t_ann in
      Builder.end_block_jump t2.eval.entry (vdelta :: ve' :: args)
    end;
    begin
      match t1.access.exit with
      | Access.Fun(_, res1, x_entry, y_exit) ->
        Access.pop_discard y_exit t.access.exit;
        Access.pop_discard x_entry t2.access.entry;
        begin (* block 8 *)
          let vres, vs, _, args = Builder.begin_block3 res1 in
          let vu = Builder.project vs t.term.t_ann in
          Builder.end_block_jump t.eval.exit (vres :: vu :: args)
        end
      | _ ->
        assert false
    end;
    build_blocks ms t2;
    begin
      match t1.access.entry with
      | Access.Fun(_, apply, x_exit, y_entry) ->
        let ts = type_of_stage apply 1 in
        let td = type_of_stage apply 2 in
        begin (* block 3 *)
          let vx, ve, args = Builder.begin_block2 t2.eval.exit in
          let vu_f = Builder.project ve (Basetype.pairB t.term.t_ann (Cbvtype.code t1.term.t_type)) in
          let vu, vf = Builder.unpair vu_f in
          let vs = Builder.embed vu ts in
          let vd = Builder.embed Builder.unit td in
          Builder.end_block_jump apply (Builder.pair vf vx :: vs :: vd :: args)
        end;
        Access.push_unit_embed t.access.entry y_entry;
        Access.push_unit_embed t2.access.exit x_exit
      | _ ->
        assert false
    end
  | Fix((th, f, x, xty), s) ->
    let x_access = List.Assoc.find_exn s.context x in
    let f_access = List.Assoc.find_exn s.context f in
    begin (* eval *)
      let vgamma, vstack, args = Builder.begin_block2 t.eval.entry in
      let vclosure = Builder.embed vgamma (Cbvtype.code t.term.t_type) in
      Builder.end_block_jump t.eval.exit (vclosure :: vstack :: args)
    end;
    (* E + H *G *)
    let tcons =
      let te = Cbvtype.multiplicity t.term.t_type in
      let tg = Cbvtype.multiplicity (List.Assoc.find_exn s.term.t_context f) in
      let thg = Basetype.pairB th tg in
      Basetype.newty (Basetype.DataB(Basetype.Data.sumid 2, [te; thg])) in
    let build_singleton ve =
      Builder.embed (Builder.inj 0 ve tcons) th in
    let build_push vh vg =
      Builder.embed (Builder.inj 1 (Builder.pair vh vg) tcons) th in
    let stack_singleton src dst =
      Access.iter2_exn src dst
        ~f:(fun (ls, ds) (ld, _) ->
            (* 2 to include E on stack! *)
            let ww, args = focus (ds + 2) (Builder.begin_block ls) in
            match ww with
            | ve :: vv ->
              let vh = build_singleton ve in
              Builder.end_block_jump ld (unfocus (vh :: vv) args)
            | _ -> assert false) in
    let stack_push src dst =
      Access.iter2_exn src dst
        ~f:(fun (ls, ds) (ld, _) ->
            (* 3 to include H, E on stack! *)
            let ww, args = focus (ds + 3) (Builder.begin_block ls) in
            match ww with
            | vh :: vg :: vv ->
              let vpushed = build_push vh vg in
              Builder.end_block_jump ld (unfocus (vpushed :: vv) args)
            | _ -> assert false) in
    let stack_case src dst1 dst2 =
      Access.iter2_list_exn src [dst1; dst2]
        ~f:(fun (la, da) ls ->
            match ls with
            | [(dst1, _); (dst2, _)] ->
              begin
                (* 2 to include H on stack!*)
                let ww, args = focus (da + 2) (Builder.begin_block la) in
                match ww with
                | [] -> assert false
                | vh :: vv ->
                  let vcons = Builder.project vh tcons in
                  Builder.end_block_case vcons
                    [ (fun ve -> dst1, unfocus (ve :: vv) args);
                      (fun vhg ->
                         let vh, vg = Builder.unpair vhg in
                         dst2, unfocus (vh :: vg :: vv) args)
                    ]
              end
            | _ -> assert false) in
    (* eval *)
    let eval_body_block =
      let ts = s.term.t_ann in
      let td = Cbvtype.code t.term.t_type in
      let tx = Cbvtype.code xty in
      fresh_label (ts :: th :: ms) "fix_eval_body" None (Basetype.pairB td tx) in
    begin
      let vdx, va, vh, args = Builder.begin_block3 eval_body_block in
      let vd, vx = Builder.unpair vdx in
      let vgamma = Builder.project vd (Context.code t.term.t_context) in
      let vdelta =
        Context.encode s.term.t_context
          ((x, vx) :: (f, vd) :: Context.decode t.term.t_context vgamma) in
      Builder.end_block_jump s.eval.entry (vdelta :: va :: vh :: args)
    end;
    (* body *)
    build_blocks (th :: ms) s;
    (* access entry *)
    begin
      match t.access.entry with
      | Access.Fun(_, eval, arg_exit, res_entry) ->
        begin
          let vr, va, ve, args = Builder.begin_block3 eval in
          let vh = build_singleton ve in
          Builder.end_block_jump eval_body_block (vr :: va :: vh :: args)
        end;
        stack_singleton arg_exit x_access.exit;
        stack_singleton res_entry s.access.entry
      | _ ->
        assert false
    end;
    (* s eval exit *)
    begin
      match t.access.exit, f_access.exit with
      | Access.Fun(_, res, arg_exit, res_entry),
        Access.Fun(_, rec_call, _, _) ->
        begin
          let vm, va, vh, args = Builder.begin_block3 s.eval.exit in
          let vcons = Builder.project vh tcons in
          Builder.end_block_case
            vcons
            [ (fun ve -> res, (vm :: va :: ve :: args));
              (fun vhg ->
                 let vh, vg = Builder.unpair vhg in
                 rec_call, (vm :: va :: vg :: vh :: args))
            ]
        end
      | _ ->
        assert false
    end;
    begin
      match t.access.entry, f_access.entry with
      | Access.Fun(_, eval, arg_exit, res_entry),
        Access.Fun(_, rec_eval, rec_arg_exit, rec_res_entry) ->
        begin
          let vm, va, vg, vh, args = Builder.begin_block4 rec_eval in
          let vpushed = build_push vh vg in
          Builder.end_block_jump eval_body_block (vm :: va :: vpushed :: args)
        end;
        stack_push rec_arg_exit x_access.exit;
        stack_push rec_res_entry s.access.entry
      | _ ->
        assert false
    end;

    begin
      match t.access.exit, f_access.exit with
      | Access.Fun(_, res, arg_entry, res_exit),
        Access.Fun(_, rec_res, rec_arg_entry, rec_res_exit) ->
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
      let vgamma, vstack, args = Builder.begin_block2 t.eval.entry in
      let vclosure = Builder.embed vgamma (Cbvtype.code t.term.t_type) in
      Builder.end_block_jump t.eval.exit (vclosure :: vstack :: args)
    end;
    begin
      match t.access.entry with
      | Access.Fun(_, eval, a1, a2) ->
        begin (* eval_body *)
          let vdx, va, ve, args = Builder.begin_block3 ~may_append:false eval in
          let vd, vx = Builder.unpair vdx in
          let vgamma = Builder.project vd (Context.code t.term.t_context) in
          let vdelta =
            Context.encode s.term.t_context
              ((x, vx) :: (f, vd) :: Context.decode t.term.t_context vgamma) in
          let vh = Builder.embed (Builder.pair ve va) th in
          let vu = Builder.embed Builder.unit s.term.t_ann in
          Builder.end_block_jump s.eval.entry (vdelta :: vu :: vh :: args)
        end;
      | _ ->
        assert false
    end;
    let gamma = List.filter s.context ~f:(fun (y, _) -> y <> x && y <> f) in
    project_context t.context gamma;
    build_blocks (th :: ms) s;
    embed_context t.context gamma;
    begin
      match t.access.exit with
      | Access.Fun(_, res, a1, a2) ->
        let ta = type_of_stage res 1 in
        let te = type_of_stage res 2 in
        let x_access = List.Assoc.find_exn s.context x in
        Access.unreachable s.access.exit;
        Access.unreachable x_access.entry;
        begin (* s eval exit *)
          let vm, vu, vh, args = Builder.begin_block3 s.eval.exit in
          let vea = Builder.project vh (Basetype.pairB te ta) in
          let ve, va = Builder.unpair vea in
          Builder.end_block_jump res (vm :: va :: ve :: args)
        end;
      | _ ->
        assert false
    end;
    let f_access = List.Assoc.find_exn s.context f in
    begin
      match t.access.entry, f_access.entry with
      | Access.Fun(_, eval, a1, a2),
        Access.Fun(_, feval, b1, b2) ->
        let ta = type_of_stage eval 1 in
        let te = type_of_stage eval 2 in
        begin (* f access entry *)
          let vm, vs, vg, vh, args = Builder.begin_block4 feval in
          let vea = Builder.project vh (Basetype.pairB te ta) in
          let ve, va = Builder.unpair vea in
          Builder.end_block_jump eval (vm :: va :: ve :: args)
        end
      | _ ->
        assert false
    end
  | Pair(t1, t2) ->
    begin (* eval *)
      let vgammadelta, vu, args = Builder.begin_block2 t.eval.entry in
      let vgamma = Context.build_map t.term.t_context t1.term.t_context vgammadelta in
      let vdelta = Context.build_map t.term.t_context t2.term.t_context vgammadelta in
      let embed_val = Builder.embed (Builder.pair vu vdelta) t1.term.t_ann in
      Builder.end_block_jump t1.eval.entry (vgamma :: embed_val :: args)
    end;
    (* access entry *)
    begin
      match t.access.entry with
      | Access.Tuple([a1; a2]) ->
        Access.pop_embed a1 t1.access.entry;
        Access.pop_embed a2 t2.access.entry
      | _ ->
        assert false
    end;
    build_blocks ms t1;
    build_blocks ms t2;
    begin (* block 2 *)
      let vf, ve, args = Builder.begin_block2 t1.eval.exit in
      let vu_delta = Builder.project ve
          (Basetype.pairB t.term.t_ann (Context.code t2.term.t_context)) in
      let vu, vdelta = Builder.unpair vu_delta in
      let vu_f = Builder.pair vu vf in
      let ve' = Builder.embed vu_f t2.term.t_ann in
      Builder.end_block_jump t2.eval.entry (vdelta :: ve' :: args)
    end;
    begin (* block 3*)
      let v2, ve, args = Builder.begin_block2 t2.eval.exit in
      let vu_f = Builder.project ve (Basetype.pairB t.term.t_ann
                                       (Cbvtype.code t1.term.t_type)) in
      let vu, v1 = Builder.unpair vu_f in
      Builder.end_block_jump t.eval.exit (Builder.pair v1 v2 :: vu :: args)
    end;
    (* access exit *)
    begin
      match t.access.exit with
      | Access.Tuple([a1; a2]) ->
        Access.project_push t1.access.exit a1;
        Access.project_push t2.access.exit a2
      | _ ->
        assert false
    end
  | Proj(t1, i) ->
    begin (* eval entry *)
      let args = Builder.begin_block t.eval.entry in
      Builder.end_block_jump t1.eval.entry args
    end;
    (* access entry *)
    begin
      match t1.access.entry with
      | Access.Tuple(xs) ->
        let xi = List.nth_exn xs i in
        (* push multiplicity of pair type *)
        Access.push_unit_embed t.access.entry xi
      | _ ->
        assert false
    end;
    (* Body *)
    build_blocks ms t1;
    begin (* eval exit *)
      let vp, vm, args = Builder.begin_block2 t1.eval.exit in
      let vp1 = Builder.proj vp i in
      Builder.end_block_jump t.eval.exit (vp1 :: vm :: args)
    end;
    (* access exit *)
    begin
      match t1.access.exit with
      | Access.Tuple(xs) ->
        (* discard multiplicity of pair type *)
        List.iteri xs
          ~f:(fun j xj ->
            if i = j then
              Access.pop_discard xj t.access.exit
            else
              Access.unreachable xj)
      | _ ->
        assert false
    end
  | If(tc, t1, t2) ->
    begin (* eval 1 *)
      let vgamma, vstack, args = Builder.begin_block2 t.eval.entry in
      let vgammac = Context.build_map t.term.t_context tc.term.t_context vgamma in
      let vgamma1 = Context.build_map t.term.t_context t1.term.t_context vgamma in
      let vgamma2 = Context.build_map t.term.t_context t2.term.t_context vgamma in
      let vstack1 = Builder.embed (Builder.tuple [vstack; vgamma1; vgamma2]) tc.term.t_ann in
      Builder.end_block_jump tc.eval.entry (vgammac :: vstack1 :: args)
    end;
    build_blocks ms tc;
    begin (* eval c *)
      let vz, vstack1, args = Builder.begin_block2 tc.eval.exit in
      let vp = Builder.project vstack1
                 (Basetype.(newty (TupleB [t.term.t_ann;
                                           Context.code t1.term.t_context;
                                           Context.code t2.term.t_context]))) in
      match Builder.untuple vp with
      | [vstack; vgamma1; vgamma2] ->
        Builder.end_block_case vz
          [ (fun _ -> t1.eval.entry, (vgamma1 :: vstack :: args));
            (fun _ -> t2.eval.entry, (vgamma2 :: vstack :: args)) ]
      | _ -> assert false
    end;
    split_entry t.access.entry t1.access.entry t2.access.entry;
    build_blocks ms t1;
    build_blocks ms t2;
    begin (* eval rt *)
      let vn, vstack, args = Builder.begin_block2 t1.eval.exit in
      let vc = join_code `Left vn t1.access.entry t2.access.entry t.access.entry in
      Builder.end_block_jump t.eval.exit (vc :: vstack :: args)
    end;
    begin (* eval rf *)
      let vn, vstack, args = Builder.begin_block2 t2.eval.exit in
      let vc = join_code `Right vn t1.access.entry t2.access.entry t.access.entry in
      Builder.end_block_jump t.eval.exit (vc :: vstack :: args)
    end;
    (* access c *)
    Access.unreachable tc.access.exit;
    join_exit t1.access.exit t2.access.exit t.access.exit

let to_ssa t =
  Builder.reset();
  let ms = [] in
  let f = add_interface ms t in
  build_blocks ms f;
  let ret_ty = type_of_stage f.eval.exit 0 in
  (* return *)
  let v, arg = Builder.begin_block1 f.eval.exit in
  Builder.end_block_return v;
  (* access exit *)
  Access.unreachable f.access.exit;
  Ssa.make
    ~func_name:"main"
    ~entry_label:f.eval.entry
    ~blocks: Builder.blocks
    ~return_type: ret_ty
