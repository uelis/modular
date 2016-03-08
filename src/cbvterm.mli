(** Typed representation of intput terms *)

type const = Ast.const

type ('a, 'b) sgn =
  | Var of Ident.t
  | Const of const * ('a list)
  | Contr of ((Ident.t * 'b) * Ident.t list) * 'a
  | Fun of (Ident.t * 'b) * 'a
  | App of 'a * 'a
  | Pair of 'a * 'a
  | Proj of 'a * int
  | If of 'a * 'a * 'a
  | Fix of (Basetype.t * Ident.t * Ident.t * 'b) * 'a
  | Tailfix of (Basetype.t * Ident.t * Ident.t * 'b) * 'a

type 'a term = {
  t_id: Ident.t;
  t_desc: ('a term, 'a) sgn;
  t_ann: Basetype.t;
  t_type: 'a;
  t_context: (Ident.t * 'a) list;
  t_loc: Ast.Location.t
  }

type t = Cbvtype.t term
