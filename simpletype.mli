open Core_kernel.Std

type 'a sgn =
  | Bool
  | Nat
  | Fun of 'a * 'a
with sexp

include Uftype.S with type 'a Sgn.t = 'a sgn

val to_string: ?concise:bool -> t -> string
