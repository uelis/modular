open Core_kernel.Std

type 'a sgn =
  | Bool
  | Nat
  | Pair of 'a * 'a
  | Fun of 'a * 'a
  [@@deriving sexp]

include Uftype.S with type 'a Sgn.t = 'a sgn
