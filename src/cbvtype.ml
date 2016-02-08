open Core_kernel.Std

type 'a sgn =
  | Bool of Basetype.t
  | Nat of Basetype.t
  | Pair of Basetype.t * ('a * 'a)
  | Fun of Basetype.t * ('a * Basetype.t * Basetype.t * 'a)
  [@@deriving sexp]

module Sig = struct

  type 'a t = 'a sgn [@@deriving sexp]

  let map (f : 'a -> 'b) (t : 'a t) : 'b t =
    match t with
    | Bool(a) -> Bool(a)
    | Nat(a) -> Nat(a)
    | Pair(a, (x, y)) -> Pair(a, (f x, f y))
    | Fun(c, (x, a, b, y)) -> Fun(c, (f x, a, b, f y))

  let children (t: 'a t) : 'a list =
    match t with
    | Bool _ -> []
    | Nat _ -> []
    | Pair (_, (x, y)) -> [x; y]
    | Fun (_, (x, _, _, y)) -> [x; y]

  let equals (s: 'a t) (t: 'a t) ~equals:(eq: 'a -> 'a -> bool) : bool =
    match s, t with
    | Bool(a1), Bool(a2)
    | Nat(a1), Nat(a2) ->
       Basetype.equals a1 a2
    | Pair(a1, (x1, y1)), Pair(a2, (x2, y2)) ->
      Basetype.equals a1 a2 &&
      eq x1 x2 &&
      eq y1 y2
    | Fun(c1, (x1, a1, b1, y1)), Fun(c2, (x2, a2, b2, y2)) ->
      Basetype.equals c1 c2 &&
      Basetype.equals a1 a2 &&
      Basetype.equals b1 b2 &&
      eq x1 x2 &&
      eq y1 y2
    | Bool _, _
    | Nat _, _
    | Pair _, _
    | Fun _, _ -> false

  let unify_exn (s: 'a t) (t: 'a t) ~unify:(unify: 'a -> 'a -> unit) : unit =
    match s, t with
    | Bool(a1), Bool(a2)
    | Nat(a1), Nat(a2) ->
      Basetype.unify_exn a1 a2
    | Pair(a1, (x1, y1)), Pair(a2, (x2, y2)) ->
      Basetype.unify_exn a1 a2;
      unify x1 x2;
      unify y1 y2
    | Fun(c1, (x1, a1, b1, y1)), Fun(c2, (x2, a2, b2, y2)) ->
      Basetype.unify_exn c1 c2;
      Basetype.unify_exn a1 a2;
      Basetype.unify_exn b1 b2;
      unify x1 x2;
      unify y1 y2
    | Bool _, _
    | Nat _, _
    | Pair _, _
    | Fun _, _ -> raise Uftype.Constructor_mismatch
end

module Cbvtype = Uftype.Make(Sig)
include Cbvtype

let rec code (a : Cbvtype.t) : Basetype.t =
  match Cbvtype.case a with
  | Cbvtype.Var -> failwith "code"
  | Cbvtype.Sgn s ->
     match s with
     | Bool _ -> Basetype.boolB
     | Nat _ -> Basetype.newty Basetype.IntB
     | Pair (_, (x, y)) -> Basetype.newty (Basetype.PairB(code x, code y))
     | Fun(_, (_, _, d, _)) -> d

let multiplicity (a : Cbvtype.t) : Basetype.t =
  match Cbvtype.case a with
  | Cbvtype.Var -> failwith "multiplicity"
  | Cbvtype.Sgn s ->
    match s with
    | Bool(c)
    | Nat(c)
    | Pair(c, _)
    | Fun(c, _) -> c
