open Core.Std
open Intlib
(** Term representation *)

module Location = struct
  type pos = { column: int; line: int}
  type loc = {start_pos: pos; end_pos: pos}
  type t = loc option
  let none = None
end

type const =
  | Cintconst of int
  | Cintadd
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
  | Ifz of t * t * t
  | Fix of Ident.t * Ident.t * t

let mkTerm d = { desc = d; loc = None }

let rec free_vars (term: t) : Ident.t list =
  let abs x l = List.filter l ~f:(fun z -> not (z = x)) in
  match term.desc with
  | Const(_, ts) -> List.concat_map ~f:free_vars ts
  | Var x -> [x]
  | Fun (x, t) -> abs x (free_vars t)
  | App (s, t) -> (free_vars s) @ (free_vars t)
  | Ifz (s, t1, t2) -> free_vars s @ free_vars t1 @ free_vars t2
  | Fix (f, x, t) -> abs f (abs x (free_vars t))

let rec all_vars (term: t) : Ident.t list =
  match term.desc with
  | Const(_, ts) -> List.concat_map ~f:all_vars ts
  | Var x -> [x]
  | Fun (x, t) -> x :: (all_vars t)
  | App (s, t) -> (all_vars s) @ (all_vars t)
  | Ifz (s, t1, t2) -> all_vars s @ all_vars t1 @ all_vars t2
  | Fix (f, x, t) -> f :: x :: all_vars t

let rename_vars (f: Ident.t -> Ident.t) (term: t) : t =
  let rec rn term =
    match term.desc with
    | Const(c, ts) -> { term with desc = Const(c, List.map ts ~f:rn) }
    | Var x -> { term with desc = (Var(f x)) }
    | Fun (x, t) -> { term with desc = (Fun(f x, rn t)) }
    | App (s, t) -> { term with desc = (App(rn s, rn t)) }
    | Ifz (s, t1, t2) -> { term with desc = (Ifz(rn s, rn t1, rn t2)) }
    | Fix (g, x, t) -> { term with desc = (Fix(f g, f x, rn t)) }
  in rn term

let variant = rename_vars Ident.variant

(* Substitues [s] for [x].
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
    | Ifz (s, t1, t2) -> 
      { term with desc = Ifz(sub sigma s, sub sigma t1, sub sigma t2) }
    | Fix (f, x, t) ->
       match abs_list sigma ([f; x], t) with
       | [f'; x'], t' ->
          { term with desc = Fix(f', x', t') }
       | _ ->
          assert false
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

let head_subst (s: t) (x: Ident.t) (t: t) : t option =
  substitute ~head:true s x t

let subst (s: t) (x: Ident.t) (t: t) : t =
  match substitute ~head:false s x t with
  | None -> t
  | Some t' -> t'

let freshen_type_vars t = t
