(** Variable names *)

open Core_kernel

module T = struct
  type t = {
    name: string;
    index: int
  } [@@deriving sexp]

  let compare (x: t) (y: t): int =
    let i = Int.compare x.index y.index in
    if i = 0 then String.compare x.name y.name else i

  let equal (x: t) (y: t) =
    Int.equal x.index y.index && String.equal x.name y.name

  let hash (x: t) : int =
    31 * (String.hash x.name) + x.index
end

include T
include Comparable.Make(T)
module Table = Hashtbl.Make(T)

let next_index = ref 0

let global (s: string) : t  =
  { name = s; index = 0 }

let fresh (s: string) : t  =
  incr next_index;
  { name = s; index = !next_index }

let variant (x: t) : t =
  incr next_index;
  { x with index = !next_index }

let to_string (x: t) : string =
  if Int.(=) x.index 0 then x.name else x.name ^ (Int.to_string x.index)
