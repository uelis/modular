module Ident = Intlib.Ident
(** Type inference *)

(** Type contexts *)
type 'a context = (Ident.t * 'a) list

exception Typing_error of Ast.t option * string

val check_term:
  Cbvtype.t context -> Ast.t -> Cbvterm.t
