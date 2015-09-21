module Ident = Intlib.Ident
(** Type inference *)

(** Type contexts *)
type 'a context = (Ident.t * 'a) list

val check_term: Ast.t -> Cbvterm.t
