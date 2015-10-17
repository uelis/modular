%{
(** Parser *)

open Core.Std
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
%token MINUS
%token COMMA EQUALS TO
%token LAMBDA
%token FST SND
%token INTADD
%token IF THEN ELSE PRINT LET IN
%token FIX 
%token <int> NUM
%token <string> IDENT
%token <string> STRING
%token EOF

%left EQUALS
%nonassoc THEN

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
    | LET identifier EQUALS term
        {Decl.TermDecl($2, $4) }

identifier:
    | IDENT
        { Ident.global $1 }

term:
    | LAMBDA identifier TO term
        { mkAst (Fun($2, $4)) }
    | FIX identifier identifier TO term
        { mkAst (Fix($2, $3, $5)) }
    | IF term THEN term ELSE term
        { mkAst (Ifz($2, $4, $6)) }
    | LET identifier EQUALS term IN term
        { mkAst (App(mkAst (Fun($2, $6)), $4)) }
    | term_app
       { $1 }


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
    | MINUS NUM
       { mkAst (Const(Cintconst(-$2), [])) }
    | NUM
       { mkAst (Const(Cintconst($1), [])) }
    | PRINT term_atom
       { mkAst (Const(Cintprint, [$2])) }
    | INTADD LPAREN term COMMA term RPAREN
       { mkAst (Const(Cintadd, [$3; $5]))}

%%
