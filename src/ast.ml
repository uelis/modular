open Core_kernel.Std
(** Term representation *)

module Location = struct
  type pos = { column: int; line: int}
  type loc = {start_pos: pos; end_pos: pos}
  type t = loc option
  let none = None
end

type const =
  | Cprint of string
  | Cboolconst of bool
  | Cintconst of int
  | Cinteq
  | Cintlt
  | Cintadd
  | Cintsub
  | Cintmul
  | Cintdiv
  | Cintprint

type t = {
  desc: t_desc;
  loc: Location.t
}
and t_desc =
  | Const of const * (t list)
  | Var of Ident.t
  | Fun of Ident.t * t
  | App of t * t
  | Pair of t * t
  | Proj of t * int
  | If of t * t * t
  | Fix of Ident.t * Ident.t * t
  | Tailfix of Ident.t * Ident.t * t

let rec free_vars (term: t) : Ident.t list =
  let abs x l = List.filter l ~f:(fun z -> not (z = x)) in
  match term.desc with
  | Const(_, ts) -> List.concat_map ~f:free_vars ts
  | Var x -> [x]
  | Fun(x, t) -> abs x (free_vars t)
  | App(s, t) -> (free_vars s) @ (free_vars t)
  | Pair(s, t) -> (free_vars s) @ (free_vars t)
  | Proj(t, _) -> free_vars t
  | If(s, t1, t2) -> free_vars s @ free_vars t1 @ free_vars t2
  | Fix(f, x, t) -> abs f (abs x (free_vars t))
  | Tailfix(f, x, t) -> abs f (abs x (free_vars t))

(** Substitues [s] for [x].
   Returns [None] if [t] does not contain [x].
   If [head] is true then only the head occurrence is subtituted.
*)
let substitute ?head:(head=false) (s: t) (x: Ident.t) (t: t) : t option =
  (* Below sigma is always a permutation that maps bound
   * variables of t to suitably fresh variables. *)
  let fvs = free_vars s in
  let apply sigma y =
    List.Assoc.find sigma y
    |> Option.value ~default:y in
  let substituted = ref false in
  let rec sub sigma term =
    match term.desc with
    | Var(y) ->
      (* substitute only once if head *)
      if x = y && ((not head) || (not !substituted)) then
        (substituted := true; s)
      else
        { term with desc = Var(apply sigma y) }
    | Const (c, ts) ->
      { term with desc = Const(c, List.map ts ~f:(sub sigma)) }
    | Fun (x, t) ->
      let (x', t') = abs sigma (x, t) in
      { term with desc = Fun(x', t') }
    | App (s, t) ->
      { term with desc = App(sub sigma s, sub sigma t) }
    | Pair (s, t) ->
      { term with desc = Pair(sub sigma s, sub sigma t) }
    | Proj (t, i) ->
      { term with desc = Proj(sub sigma t, i) }
    | If (s, t1, t2) ->
      { term with desc = If(sub sigma s, sub sigma t1, sub sigma t2) }
    | Fix (f, x, t) ->
      begin
        match abs_list sigma ([f; x], t) with
        | [f'; x'], t' ->
          { term with desc = Fix(f', x', t') }
        | _ ->
          assert false
      end
    | Tailfix (f, x, t) ->
      begin
        match abs_list sigma ([f; x], t) with
        | [f'; x'], t' ->
          { term with desc = Tailfix(f', x', t') }
        | _ ->
          assert false
      end
  and abs sigma (y, u) =
    match abs_list sigma ([y], u) with
    | [y'], u -> y', u
    | _ -> assert false
  and abs_list sigma (l, t1) =
    if List.mem l x then (l, t1)
    else if List.for_all l ~f:(fun y -> not (List.mem fvs y)) then
      (* no capture *)
      (l, sub sigma t1)
    else
      (* avoid capture *)
      let l' = List.map ~f:Ident.variant l in
      (l', sub ((List.zip_exn l l') @ sigma) t1)
  in
  let result = sub [] t in
  if (!substituted) then Some result else None

let subst (s: t) (x: Ident.t) (t: t) : t =
  match substitute ~head:false s x t with
  | None -> t
  | Some t' -> t'
