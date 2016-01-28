(** Source terms *)
  
(** Location of term in the source file *)
module Location : sig
  type pos = { column: int; line: int}
  type loc = {start_pos: pos; end_pos: pos}
  type t = loc option
  val none: t
end

type const =
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
  | Fst of t
  | Snd of t
  | Ifz of t * t * t
  | Fix of Ident.t * Ident.t * t
  | Tailfix of Ident.t * Ident.t * t

(** Capture avoiding substitution.
    [subst s x t] substitues [s] for [x] in [t]. *)
val subst: t -> Ident.t -> t -> t
