(** Type inference *)
open Core_kernel.Std

type 'a sgn =
  | Bool
  | Nat
  | Pair of 'a * 'a
  | Fun of 'a * 'a
  [@@deriving sexp]

module Sig = struct

  type 'a t = 'a sgn [@@deriving sexp]

  let map (f : 'a -> 'b) (t : 'a t) : 'b t =
    match t with
    | Bool -> Bool
    | Nat -> Nat
    | Pair(x, y) -> Pair(f x, f y)
    | Fun(x, y) -> Fun(f x, f y)

  let children (t: 'a t) : 'a list =
    match t with
    | Bool
    | Nat -> []
    | Pair(x, y) -> [x; y]
    | Fun(x, y) -> [x; y]

  let equals (s: 'a t) (t: 'a t) ~equals:(eq: 'a -> 'a -> bool) : bool =
    match s, t with
    | Bool, Bool
    | Nat, Nat ->
      true
    | Pair(x1, y1), Pair(x2, y2) ->
      eq x1 x2 && eq y1 y2
    | Fun(x1, y1), Fun(x2, y2) ->
      eq x1 x2 && eq y1 y2
    | Bool, _
    | Nat, _
    | Pair _, _
    | Fun _, _ -> false

  let unify_exn (s: 'a t) (t: 'a t) ~unify:(unify: 'a -> 'a -> unit) : unit =
    match s, t with
    | Bool, Bool
    | Nat, Nat ->
      ()
    | Pair(x1, y1), Pair(x2, y2) ->
      unify x1 x2;
      unify y1 y2
    | Fun(x1, y1), Fun(x2, y2) ->
      unify x1 x2;
      unify y1 y2
    | Bool, _
    | Nat, _
    | Pair _, _
    | Fun _, _ -> raise Uftype.Constructor_mismatch
end

include Uftype.Make(Sig)
