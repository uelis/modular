(** Simple main program. *)
open Core_kernel.Std
open Lexing

let parse_error_loc lexbuf =
  let start_pos = lexbuf.lex_start_p in
  Printf.sprintf "line %i, character %i:"
    (start_pos.pos_lnum) (start_pos.pos_cnum - start_pos.pos_bol + 1)

let error_msg loc msg = if loc = "" then msg else loc ^ " " ^ msg
let exit_with_error loc msg =
  Printf.printf "%s\n%!" (error_msg loc msg);
  exit 1
let line_column_loc (line : int) (column : int ) =
  Printf.sprintf "line %i, column %i:" line column

let parse (s: string) : Decl.t list =
  let lexbuf = Lexing.from_string s in
  try
    Parser.decls Lexer.main lexbuf
  with
  | Parsing.Parse_error ->
    exit_with_error (parse_error_loc lexbuf) "Parse error"
  | Decl.Illformed_decl(msg, l, c) ->
    exit_with_error (line_column_loc l c) ("Syntax error. " ^ msg)

(* For error reporting: compute a string of where the error occurred *)
let term_loc (s : Ast.Location.t option) =
  match s with
  | None -> ""
  | Some s ->
    let open Ast in
    let open Ast.Location in
    match s with
    | Some(loc) when loc.start_pos.line = loc.end_pos.line ->
      Printf.sprintf "line %i, columns %i-%i:"
        loc.start_pos.line loc.start_pos.column loc.end_pos.column
    | Some(loc) ->
      Printf.sprintf "line %i, column %i to line %i, column %i:"
        loc.start_pos.line loc.start_pos.column
        loc.end_pos.line loc.end_pos.column
    | None -> ""

let compile (d: Decl.t) : unit =
  match d with
  | Decl.TermDecl(f, ast) ->
    let f_name = Ident.to_string f in
    try
      let t = Typing.check_term ast in
      Printf.printf "%s : %s%!\n"
        (Ident.to_string f)
        (Printing.string_of_cbvtype
           ~concise:(not !Opts.print_type_details)
           t.Cbvterm.t_type);
      if !Opts.print_annotated_term then
        Printing.fprint_annotated_term Format.std_formatter t;
      let ssa = Translate.to_ssa t in
(*      Out_channel.with_file
        (f_name ^ ".ssa")
        ~f:(fun c -> Ssa.fprint_func c ssa) *)
      let ssa_traced = Trace.trace ssa in
      let ssa_shortcut = Trace.shortcut_jumps ssa_traced in
(*      Out_channel.with_file
        (f_name ^ ".opt.ssa")
        ~f:(fun c -> Ssa.fprint_func c ssa_shortcut);*)
      let llvm_module = Llvmcodegen.llvm_compile ssa_shortcut in
      let target = Printf.sprintf "%s.bc" f_name in
      ignore (Llvm_bitwriter.write_bitcode_file llvm_module target)
    with Simpletyping.Typing_error(s, err) ->
      let msg = err ^ "\nIn declaration of '" ^ f_name ^ "'." in
      raise (Failure (error_msg (term_loc s) msg))

let arg_spec =
  [("--type-details", Arg.Set Opts.print_type_details,
    "Print full type details, including subexponentials.");
   ("--verbose", Arg.Set Opts.verbose, "Print compilation details..");
   ("--print-annotated-term", Arg.Set Opts.print_annotated_term,
    "Print program term with type annotations.")
  ]

let usage_msg = "Usage: modular input.cbv\nOptions:"

let () =
  try
    let file_name = ref "" in
    Arg.parse arg_spec (fun s -> file_name := s) usage_msg;
    if !file_name = "" then
      Printf.printf "No input file.\n"
    else
      begin
        let input = In_channel.read_all !file_name in
        let decls = parse input in
        let substituted_decls = Decl.expand_all decls in
        List.iter ~f:compile substituted_decls
      end
  with
  | Sys_error msg
  | Failure msg ->
    exit_with_error "" msg
  | Simpletyping.Typing_error(t, msg)->
    exit_with_error (term_loc t) msg
