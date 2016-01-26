type t =
  | TermDecl of Ident.t * Ast.t

exception Illformed_decl of string * int * int

let expand_in_term (d: t) (s: Ast.t) : Ast.t =
  match d with
  | TermDecl(v, t) -> Ast.subst t v s

let expand (d: t) : t -> t =
  function
    | TermDecl(w, s) -> TermDecl(w, expand_in_term d s)

let rec expand_all (ds: t list) : t list =
  match ds with
    | [] -> []
    | d :: rest ->
        d :: expand_all (List.map (expand d) rest)
