(** Representation of interactive types *)
open Core_kernel.Std

type 'a sgn =
  | Bool of Basetype.t
  | Nat of Basetype.t
  | Pair of Basetype.t * ('a * 'a)
  | Fun of Basetype.t * ('a * Basetype.t * Basetype.t * 'a)
  [@@deriving sexp]

include Uftype.S with type 'a Sgn.t = 'a sgn

val code: t -> Basetype.t
val multiplicity: t -> Basetype.t

val unFun: t -> Basetype.t * (t * Basetype.t * Basetype.t * t)
val unPair: t -> Basetype.t * (t * t)
