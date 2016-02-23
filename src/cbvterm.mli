(** Typed representation of intput terms *)

type const = Ast.const

type 'a term = {
  t_id: Ident.t;
  t_desc: 'a t_desc;
  t_ann: Basetype.t;
  t_type: 'a;
  t_context: (Ident.t * 'a) list;
  t_loc: Ast.Location.t
  }
 and 'a t_desc =
   | Var of Ident.t
   | Const of const * ('a term list)
   | Contr of ((Ident.t * 'a) * Ident.t list) * 'a term
   | Fun of (Ident.t * 'a) * 'a term
   | App of 'a term * 'a term
   | Pair of 'a term * 'a term
   | Fst of 'a term
   | Snd of 'a term
   | Ifz of 'a term * 'a term * 'a term
   | Fix of (Basetype.t * Ident.t * Ident.t * 'a) * 'a term
   | Tailfix of (Basetype.t * Ident.t * Ident.t * 'a) * 'a term

type t = Cbvtype.t term
