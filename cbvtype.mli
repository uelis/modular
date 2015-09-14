(** Representation of interactive types *)

open Core.Std
module Basetype = Intlib.Basetype
module Uftype = Intlib.Uftype                    

type 'a sgn =
  | Nat of Basetype.t
  | Fun of Basetype.t * ('a * Basetype.t * Basetype.t * 'a)
with sexp

include Uftype.S with type 'a Sgn.t = 'a sgn

val code: t -> Basetype.t
val multiplicity: t -> Basetype.t

val to_string: ?concise:bool -> t -> string
