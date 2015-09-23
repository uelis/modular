open Core.Std
module Uftype = Intlib.Uftype                    

type 'a sgn =
  | Nat
  | Fun of 'a * 'a
with sexp

include Uftype.S with type 'a Sgn.t = 'a sgn

val to_string: ?concise:bool -> t -> string
