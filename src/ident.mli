open Core_kernel.Std

(** Variable names *)

type t = private {
  name: string;
  index: int
} [@@deriving sexp]

include Comparable.S with type t := t
module Table : Hashtbl.S with type key := t

val global: string -> t
val fresh: string -> t
val variant: t -> t

val to_string: t -> string
