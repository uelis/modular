type 'a context = (Ident.t * 'a) list

type linearized_term = {
  linear_term: Simpletype.t Cbvterm.term;
  subst: (Ident.t * Ident.t) list
}

exception Typing_error of Ast.Location.t option * string

val check: Ast.t -> linearized_term
