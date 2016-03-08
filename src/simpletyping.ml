(** Type inference *)
open Core_kernel.Std

type 'a context = (Ident.t * 'a) list

exception Typing_error of Ast.Location.t option * string

let eq_constraint t ~expected:expected_ty ~actual:actual_ty =
  try
    Simpletype.unify_exn expected_ty actual_ty
  with
  | Uftype.Cyclic_type ->
    let msg = "Unification leads to cyclic type." in
    raise (Typing_error(None, msg))
  | Uftype.Constructor_mismatch ->
    let msg = Printf.sprintf
                "Term has type %s, but a term of type %s is expected."
                (Simpletype.to_string actual_ty)
                (Simpletype.to_string expected_ty) in
    raise (Typing_error(Some t.Ast.loc, msg))

(* Invariant: All variables defined in subst have a free occurrence
   in the term. *)
type linearized_term = {
  linear_term: Simpletype.t Cbvterm.term;
  subst: (Ident.t * Ident.t) list
}

let contract_instances
      ((x: Ident.t), (a: Simpletype.t))
      (t: linearized_term)
  : linearized_term =
  let open Cbvterm in
  let xs, sigma =
    List.partition_map
      t.subst
      ~f:(fun (y, y') -> if x = y then `Fst y' else `Snd (y, y')) in
  let xs_types, gamma =
    List.partition_map
      t.linear_term.t_context
      ~f:(fun (y, a) -> if List.mem xs y then `Fst a else `Snd (y, a)) in
  List.iter xs_types
    ~f:(fun b -> Simpletype.unify_exn a b);
  { linear_term = {
      t.linear_term with
      t_id = Ident.fresh "id";
      t_desc = Contr(((x, a), xs), t.linear_term);
      t_ann = Basetype.newvar ();
      t_context = (x, a) :: gamma
    };
    subst = sigma
  }

let arg_types c =
  match c with
  | Ast.Cboolconst _
  | Ast.Cintconst _ -> []
  | Ast.Cinteq
  | Ast.Cintlt
  | Ast.Cintadd
  | Ast.Cintsub
  | Ast.Cintmul
  | Ast.Cintdiv ->
    let nat = Simpletype.newty Simpletype.Nat in
    [nat; nat]
  | Ast.Cintprint ->
    let nat = Simpletype.newty Simpletype.Nat in
    [nat]

let ret_type c =
  match c with
  | Ast.Cintconst _
  | Ast.Cintadd
  | Ast.Cintsub
  | Ast.Cintmul
  | Ast.Cintdiv
  | Ast.Cintprint ->
    Simpletype.newty Simpletype.Nat
  | Ast.Cboolconst _
  | Ast.Cinteq
  | Ast.Cintlt ->
    Simpletype.newty Simpletype.Bool

let rec linearize (phi: Simpletype.t context) (t: Ast.t)
  : linearized_term =
  let open Cbvterm in
  match t.Ast.desc with
  | Ast.Var(v: Ident.t) ->
    let a =
      match List.Assoc.find phi v with
      | Some a -> a
      | None ->
        let msg = "Variable '" ^ (Ident.to_string v) ^ "' not bound." in
        raise (Typing_error (Some t.Ast.loc, msg)) in
    let v' = Ident.variant v in
    { linear_term = {
        t_id = Ident.fresh "id";
        t_desc = Cbvterm.Var(v');
        t_ann = Basetype.newvar ();
        t_type = a;
        t_context = [(v', a)];
        t_loc = t.Ast.loc
      };
      subst = [(v, v')]
    }
  | Ast.Const(c, args) ->
    let args_with_expected_types =
      match List.zip args (arg_types c) with
      | Some a -> a
      | None ->
        let msg = "Wrong number of arguments to primitive operation." in
        raise (Typing_error (Some t.Ast.loc, msg))
    in
    let linearized_args = List.map ~f:(linearize phi) args in
    List.iter2_exn args_with_expected_types linearized_args
      ~f:(fun (a, t) sa ->
        eq_constraint a ~actual:sa.linear_term.t_type ~expected:t);
    let args_linear_term = List.map linearized_args ~f:(fun s -> s.linear_term) in
    let context = List.concat_map args_linear_term ~f:(fun t -> t.t_context) in
    let subst = List.concat_map linearized_args ~f:(fun s -> s.subst) in
    { linear_term = {
        t_id = Ident.fresh "id";
        t_desc = Const(c, args_linear_term);
        t_ann = Basetype.newvar ();
        t_type = ret_type c;
        t_context = context;
        t_loc = t.Ast.loc
      };
      subst = subst
    }
  | Ast.Pair(s, t) ->
    let sl = linearize phi s in
    let tl = linearize phi t in
    { linear_term = {
        t_id = Ident.fresh "id";
        t_desc = Pair(sl.linear_term, tl.linear_term);
        t_ann = Basetype.newvar ();
        t_type = Simpletype.newty
                   (Simpletype.Pair(sl.linear_term.t_type, tl.linear_term.t_type));
        t_context = sl.linear_term.t_context @ tl.linear_term.t_context;
        t_loc = t.Ast.loc
      };
      subst = sl.subst @ tl.subst
    }
  | Ast.Proj(t, i) ->
    if not (i = 0 || i = 1) then
      begin
        let msg = "projection out of range." in
        raise (Typing_error (Some t.Ast.loc, msg))
      end;
    let tl = linearize phi t in
    let alpha = Simpletype.newvar () in
    let beta = Simpletype.newvar () in
    eq_constraint t
      ~actual:tl.linear_term.t_type
      ~expected:(Simpletype.newty (Simpletype.Pair(alpha, beta)));
    { linear_term = {
        t_id = Ident.fresh "id";
        t_desc = Proj(tl.linear_term, i);
        t_ann = Basetype.newvar ();
        t_type = List.nth_exn [alpha; beta] i;
        t_context = tl.linear_term.t_context;
        t_loc = t.Ast.loc
      };
      subst = tl.subst
    }
  | Ast.App(s, t) ->
    let sl = linearize phi s in
    let tl = linearize phi t in
    let beta = Simpletype.newvar () in
    eq_constraint s
      ~actual:sl.linear_term.t_type
      ~expected:(Simpletype.newty (Simpletype.Fun(tl.linear_term.t_type, beta)));
    { linear_term = {
        t_id = Ident.fresh "id";
        t_desc = App(sl.linear_term, tl.linear_term);
        t_ann = Basetype.newvar ();
        t_type = beta;
        t_context = sl.linear_term.t_context @ tl.linear_term.t_context;
        t_loc = t.Ast.loc
      };
      subst = sl.subst @ tl.subst
    }
  | Ast.Fun(x, t) ->
    let alpha = Simpletype.newvar() in
    let tl = linearize ((x, alpha) :: phi) t in
    let body = contract_instances (x, alpha) tl in
    let sigma = List.filter body.subst ~f:(fun (y, _) -> y <> x) in
    let gamma = List.filter body.linear_term.t_context ~f:(fun (y, _) -> y <> x) in
    { linear_term = {
        t_id = Ident.fresh "id";
        t_desc = Fun((x, alpha), body.linear_term);
        t_ann = Basetype.newvar ();
        t_type = Simpletype.newty (Simpletype.Fun(alpha, body.linear_term.t_type));
        t_context = gamma;
        t_loc = t.Ast.loc
      };
      subst = sigma
    }
  | Ast.Fix(f, x, s) ->
    let alpha = Simpletype.newvar() in
    let beta = Simpletype.newvar() in
    let sl = linearize ((f, alpha) :: (x, beta) :: phi) s in
    let tl = contract_instances
               (f, alpha)
               (contract_instances (x, beta) sl) in
    let sigma = List.filter tl.subst ~f:(fun (y, _) -> y <> x && y <> f) in
    let gamma = List.filter tl.linear_term.t_context ~f:(fun (y, _) -> y <> x && y <> f) in
    let a = Simpletype.newty (Simpletype.Fun(beta, tl.linear_term.t_type)) in
    let h = Basetype.newvar () in
    eq_constraint t ~actual:a ~expected:alpha;
    { linear_term = {
        t_id = Ident.fresh "id";
        t_desc = Fix((h, f, x, beta), tl.linear_term);
        t_ann = Basetype.newvar ();
        t_type = a;
        t_context = gamma;
        t_loc = t.Ast.loc
      };
      subst = sigma
    }
  | Ast.Tailfix(f, x, s) ->
    (* TODO: verify that f appears in tail position *)
    let alpha = Simpletype.newvar() in
    let beta = Simpletype.newvar() in
    let sl = linearize ((f, alpha) :: (x, beta) :: phi) s in
    let tl = contract_instances
               (f, alpha)
               (contract_instances (x, beta) sl) in
    let sigma = List.filter tl.subst ~f:(fun (y, _) -> y <> x && y <> f) in
    let gamma = List.filter tl.linear_term.t_context ~f:(fun (y, _) -> y <> x && y <> f) in
    let a = Simpletype.newty (Simpletype.Fun(beta, tl.linear_term.t_type)) in
    let h = Basetype.newvar () in
    eq_constraint t ~actual:a ~expected:alpha;
    { linear_term = {
        t_id = Ident.fresh "id";
        t_desc = Tailfix((h, f, x, beta), tl.linear_term);
        t_ann = Basetype.newvar ();
        t_type = a;
        t_context = gamma;
        t_loc = t.Ast.loc
      };
      subst = sigma
    }
  | Ast.If(s, tt, tf) ->
    let sl = linearize phi s in
    let ttl = linearize phi tt in
    let tfl = linearize phi tf in
    eq_constraint s
      ~actual:sl.linear_term.t_type
      ~expected:(Simpletype.newty Simpletype.Bool);
    eq_constraint tt
      ~actual:tfl.linear_term.t_type
      ~expected:ttl.linear_term.t_type;
    { linear_term = {
        t_id = Ident.fresh "id";
        t_desc = If(sl.linear_term, ttl.linear_term, tfl.linear_term);
        t_ann = Basetype.newvar ();
        t_type = ttl.linear_term.t_type;
        t_context = sl.linear_term.t_context @
                    ttl.linear_term.t_context @ tfl.linear_term.t_context;
        t_loc = t.Ast.loc
      };
      subst = sl.subst @ ttl.subst @ tfl.subst
    }

let rec is_first_order (t: Simpletype.t) : bool =
  let open Simpletype in
  match case t with
  | Var -> false
  | Sgn a ->
    match a with
    | Bool | Nat -> true
    | Pair(b, c) -> is_first_order b && is_first_order c
    | Fun _ -> false

let rec check_term (t: Simpletype.t Cbvterm.term) : unit =
  let open Cbvterm in
  match t.t_desc with
  | Var _
  | Const _ ->
    ()
  | Proj(t, _)
  | Fun(_, t)
  | Fix(_, t)
  | Contr(_, t) ->
    check_term t
  | Pair(s, t)
  | App(s, t) ->
    check_term s;
    check_term t
  | If(s, tt, tf) ->
    check_term s;
    check_term tt;
    check_term tf
  | Tailfix((_, f, x, tx), s) ->
    check_term s;
    (* TODO: check that applications of f appear in tail position *)
    match Simpletype.case t.t_type with
    | Simpletype.Var -> assert false
    | Simpletype.Sgn a ->
      match a with
      | Simpletype.Bool
      | Simpletype.Nat
      | Simpletype.Pair _ ->
        assert false
      | Simpletype.Fun(tx, ty) ->
        if not (is_first_order tx && is_first_order ty) then
          begin
            let msg = "tailfix is restricted to first-order types." in
            raise (Typing_error (Some t.Cbvterm.t_loc, msg))
          end

let check (t: Ast.t) : linearized_term =
  let l = linearize [] t in
  check_term l.linear_term;
  l
