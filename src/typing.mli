(** Type inference for annotated PCF *)

(** Type contexts *)
type 'a context = (Ident.t * 'a) list

val code_of_context: Cbvtype.t context -> Basetype.t

(** Check that a given term is typeable and add type annotations. *)
val check_term: Ast.t -> Cbvterm.t
