(** Pretty printing of terms and types *)

(** Resets all previously chosen variable names for type variables
    etc. *)
val reset : unit -> unit

(** Returns a string representation of the data type with the given
    name. *)
val string_of_data : Ident.t -> string

val string_of_simpletype : Simpletype.t -> string
val string_of_basetype : Basetype.t -> string
val string_of_cbvtype : ?concise:bool -> Cbvtype.t -> string

val fprint_annotated_term: Format.formatter -> Cbvterm.t -> unit
