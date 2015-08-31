(** Typed representation of intput terms *)

module Ident = Intlib.Ident
module Basetype = Intlib.Basetype

type const = Ast.const
               
type t = {
    t_desc: t_desc;
    t_ann: Basetype.t;
    t_type: Cbvtype.t;
    t_context: (Ident.t * Cbvtype.t) list;
    t_loc: Ast.Location.t
  }
 and t_desc =
   | Var of Ident.t
   | Const of const * (t list)
   | Contr of (Ident.t * Ident.t list) * t
   | Fun of (Ident.t * Cbvtype.t) * t
   | App of t * t
   | Ifz of t * t * t
   | Fix of (Ident.t * Ident.t * Cbvtype.t) * t
