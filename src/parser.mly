%{
(** Parser *)

open Core_kernel
open Lexing
open Parsing
open Ast

let location_of_pos pos = 
  { Location.line = pos.pos_lnum;
    Location.column = pos.pos_cnum - pos.pos_bol + 1 }

let mkAst d : Ast.t =
  let s = location_of_pos (Parsing.symbol_start_pos ()) in
  let e = location_of_pos (Parsing.symbol_end_pos ()) in
  { Ast.desc = d;
    loc = Some { Location.start_pos = s;
                 Location.end_pos = e } }
%}

%token LPAREN RPAREN 
%token PLUS MINUS STAR SLASH TILDE
%token COMMA EQUALS LT GT TO
%token LAMBDA
%token FST SND
%token TRUE FALSE
%token IF THEN ELSE PRINT LET IN
%token REC TAILREC
%token <int> NUM
%token <string> IDENT
%token <string> STRING
%token EOF

%nonassoc THEN
%left EQUALS LT
%left PLUS MINUS
%left STAR SLASH
%nonassoc TILDE

%start decls
%type <Decl.t list> decls
%type <Ast.t> term

%%

decls:
    | EOF
      { [] }
    | decl decls
      { $1 :: $2 }

decl:
    | LET term_let 
       { let f, t = $2 in Decl.TermDecl(f, t) }

identifier:
    | IDENT
       { Ident.global $1 }

term:
    | LAMBDA identifier TO term
       { mkAst (Fun($2, $4)) }
    | IF term THEN term ELSE term
       { mkAst (If($2, $4, $6)) }
    | LET term_let IN term
       { let f, t = $2 in mkAst (App(mkAst (Fun(f, $4)), t)) }
    | term_inf
       { $1 }

term_let:
   | identifier EQUALS term
       { $1, $3 }
   | REC identifier identifier EQUALS term
       { $2, mkAst (Fix($2, $3, $5)) }
   | TAILREC identifier identifier EQUALS term
       { $2, mkAst (Tailfix($2, $3, $5)) }

term_inf:
    | term_app
       { $1 }
    | term_inf EQUALS term_inf
       { mkAst (Const(Cinteq, [$1; $3]))}
    | term_inf LT term_inf
       { mkAst (Const(Cintlt, [$1; $3]))}
    | term_inf PLUS term_inf
       { mkAst (Const(Cintadd, [$1; $3]))}
    | term_inf MINUS term_inf
       { mkAst (Const(Cintsub, [$1; $3]))}
    | term_inf STAR term_inf
       { mkAst (Const(Cintmul, [$1; $3]))}
    | term_inf SLASH term_inf
       { mkAst (Const(Cintdiv, [$1; $3]))}

term_app:
    | term_atom
       { $1 }
    | term_app term_atom
       { mkAst (App($1, $2))  }

term_atom:
    | identifier
       { mkAst (Ast.Var($1)) }
    | LPAREN term RPAREN
       { $2 }
    | LPAREN term COMMA term RPAREN
       { mkAst (Pair($2, $4)) }
    | TILDE NUM
       { mkAst (Const(Cintconst(-$2), [])) }
    | NUM
       { mkAst (Const(Cintconst($1), [])) }
    | TRUE
       { mkAst (Const(Cboolconst(true), [])) }
    | FALSE
       { mkAst (Const(Cboolconst(false), [])) }
    | PRINT STRING
       { mkAst (Const(Cprint($2), [])) }
    | PRINT term_atom
       { mkAst (Const(Cintprint, [$2])) }
    | FST term_atom
       { mkAst (Proj($2, 0)) }
    | SND term_atom
       { mkAst (Proj($2, 1)) }

%%
