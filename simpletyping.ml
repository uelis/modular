(** Type inference *)
open Core_kernel.Std

type 'a context = (Ident.t * 'a) list

exception Typing_error of Ast.t option * string

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
    raise (Typing_error(Some t, msg))

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
        t_desc = Contr(((x, a), xs), t.linear_term);
        t_ann = Basetype.newvar ();
        t_context = (x, a) :: gamma
      };
    subst = sigma
  }

let arg_types c =
  match c with
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
        raise (Typing_error (Some t, msg)) in
    let v' = Ident.variant v in
    { linear_term = {
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
        raise (Typing_error (Some t, msg))
    in
    let linearized_args = List.map ~f:(linearize phi) args in
    List.iter2_exn args_with_expected_types linearized_args
      ~f:(fun (a, t) sa ->
          eq_constraint a ~actual:sa.linear_term.t_type ~expected:t);
    let args_linear_term = List.map linearized_args ~f:(fun s -> s.linear_term) in
    let context = List.concat_map args_linear_term ~f:(fun t -> t.t_context) in
    let subst = List.concat_map linearized_args ~f:(fun s -> s.subst) in
    { linear_term = {
          t_desc = Const(c, args_linear_term);
          t_ann = Basetype.newvar ();
          t_type = ret_type c;
          t_context = context;
          t_loc = t.Ast.loc
        };
      subst = subst
    }
  | Ast.App(s, t) ->
    let sl = linearize phi s in
    let tl = linearize phi t in
    let beta = Simpletype.newvar () in
    eq_constraint s
      ~actual:sl.linear_term.t_type
      ~expected:(Simpletype.newty (Simpletype.Fun(tl.linear_term.t_type, beta)));
    { linear_term = {
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
          t_desc = Fix((h, f, x, beta), tl.linear_term);
          t_ann = Basetype.newvar ();
          t_type = a;
          t_context = gamma;
          t_loc = t.Ast.loc
        };
      subst = sigma
    }
  | Ast.Ifz(s, tt, tf) ->
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
          t_desc = Ifz(sl.linear_term, ttl.linear_term, tfl.linear_term);
          t_ann = Basetype.newvar ();
          t_type = ttl.linear_term.t_type;
          t_context = sl.linear_term.t_context @
                      ttl.linear_term.t_context @ tfl.linear_term.t_context;
          t_loc = t.Ast.loc
        };
      subst = sl.subst @ ttl.subst @ tfl.subst
    }
