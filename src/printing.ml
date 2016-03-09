open Core_kernel.Std
(** Conversion to strings for printing on an ansi terminal *)

let ansi_cyan = "\027[36m"
let ansi_defaultcolor = "\027[39m"

(** Printing state *)

let name_counter = ref 0
(* tables of already chosen variable names *)
let simpletype_names = Int.Table.create ()
let basetype_names = Int.Table.create ()
let cbvtype_names = Int.Table.create ()

(* Reset printing state *)
let reset () =
  name_counter := 0;
  Int.Table.clear simpletype_names;
  Int.Table.clear basetype_names;
  Int.Table.clear cbvtype_names

let new_name () =
  let i = !name_counter in
  incr(name_counter);
  let c = Char.of_int_exn (Char.to_int 'a' + i mod 26) in
  let n = i / 26 in
  if (n = 0) then
    Printf.sprintf "%c" c
  else
    Printf.sprintf "%c%i" c n;;

let get_name (table: string Int.Table.t) (id: int) : string =
  Int.Table.find_or_add table id ~default:new_name


(** Simple types *)

let name_of_simpletype_var t = get_name simpletype_names (Simpletype.repr_id t)

let string_of_simpletype (ty: Simpletype.t): string =
  let open Simpletype in
  let cycle_nodes =
    let cycles = dfs_cycles ty |> List.map ~f:repr_id in
    List.fold cycles ~init:Int.Set.empty ~f:Int.Set.add in
  let strs = Int.Table.create () in
  let rec str (t: t) l =
    let rec s l =
      match l, case t with
      | `Type, Var -> s `Atom
      | `Type, Sgn(Pair(t1, t2)) -> Printf.sprintf "%s * %s"
                                      (str t1 `Atom) (str t2 `Atom)
      | `Type, Sgn(Fun(t1, t2)) -> Printf.sprintf "%s -> %s"
                                     (str t1 `Atom) (str t2 `Type)
      | `Type, Sgn(Bool)
      | `Type, Sgn(Nat) -> s `Atom
      | `Atom, Var -> "\'" ^ (name_of_simpletype_var t)
      | `Atom, Sgn(Bool) -> "bool"
      | `Atom, Sgn(Nat) -> "nat"
      | `Atom, Sgn(Pair _)
      | `Atom, Sgn(Fun _) -> Printf.sprintf "(%s)" (s `Type) in
    let tid = repr_id t in
    match Int.Table.find strs tid with
    | Some s -> s
    | None ->
      if Int.Set.mem cycle_nodes tid then
        let alpha = "''" ^ (name_of_simpletype_var (newvar())) in
        Int.Table.set strs ~key:tid ~data:alpha;
        let s = "(rec " ^ alpha ^ ". " ^ (s l) ^ ")" in
        Int.Table.set strs ~key:tid ~data:s;
        s
      else
        s l in
  str ty `Type


(** Base types *)

let name_of_basetype_var t = get_name basetype_names (Basetype.repr_id t)

let string_of_basetype (ty: Basetype.t): string =
  let open Basetype in
  let cycle_nodes =
    let cycles = Basetype.dfs_cycles ty |> List.map ~f:Basetype.repr_id in
    List.fold cycles ~init:Int.Set.empty ~f:Int.Set.add in
  let strs = Int.Table.create () in
  let rec str (t: Basetype.t) l =
    let rec s l =
      match l, case t with
      | `Summand, Var -> s `Atom
      | `Summand, Sgn(DataB(id, [])) when id = Data.sumid 0 -> "void"
      | `Summand, Sgn(DataB(id, [t1; t2])) when id = Data.sumid 2 ->
        Printf.sprintf "%s + %s" (str t1 `Summand) (str t2 `Atom)
      | `Summand, Sgn(DataB(id, [])) -> Ident.to_string id
      | `Summand, Sgn(DataB(id, params)) ->
        Printf.sprintf "%s<%s>" (Ident.to_string id)
          (List.map params ~f:(fun t2 -> str t2 `Summand)
           |> String.concat ~sep:", ")
      | `Summand, Sgn(TupleB([])) -> "()"
      | `Summand, Sgn(TupleB(ts)) ->
        String.concat ~sep:" * " (List.map ~f:(fun t -> str t `Atom) ts)
      | `Summand, Sgn(IntB)
      | `Summand, Sgn(BoxB _) -> s `Atom
      | `Atom, Var -> "\'" ^ (name_of_basetype_var t)
      | `Atom, Sgn(IntB) -> "int"
      | `Atom, Sgn(BoxB(b)) ->  Printf.sprintf "box<%s>" (str b `Summand)
      | `Atom, Sgn(TupleB([])) -> "()"
      | `Atom, Sgn(DataB _)
      | `Atom, Sgn(TupleB _) -> Printf.sprintf "(%s)" (s `Summand) in
    let tid = repr_id t in
    match Int.Table.find strs tid with
    | Some s -> s
    | None ->
      if Int.Set.mem cycle_nodes tid then
        let alpha = "'" ^ (name_of_basetype_var (newvar())) in
        Int.Table.set strs ~key:tid ~data:alpha;
        let s = "(rec " ^ alpha ^ ". " ^ (s l) ^ ")" in
        Int.Table.set strs ~key:tid ~data:s;
        s
      else
        s l in
  str ty `Summand

let string_of_data id =
  let buf = Buffer.create 80 in
  let name = id in
  let cnames = Basetype.Data.constructor_names id in
  let nparams = Basetype.Data.param_count id in
  let params = List.init nparams ~f:(fun _ -> Basetype.newvar()) in
  let ctypes = Basetype.Data.constructor_types id params in
  let cs = List.zip_exn cnames ctypes in
  Buffer.add_string buf "type ";
  Buffer.add_string buf (Ident.to_string name);
  if (nparams > 0) then begin
    Buffer.add_string buf "<";
    Buffer.add_string buf (String.concat ~sep:","
                             (List.map ~f:string_of_basetype params));
    Buffer.add_string buf ">";
  end;
  Buffer.add_string buf " = ";
  Buffer.add_string buf
    (String.concat ~sep:" | "
       (List.map cs ~f:(fun (n, t) ->
            Printf.sprintf "%s of %s"
              (Ident.to_string n) (string_of_basetype t))));
  Buffer.contents buf

(** cbv types *)

let name_of_cbvtypevar t = get_name cbvtype_names (Cbvtype.repr_id t)

let string_of_cbvtype ?concise:(concise=true) (ty: Cbvtype.t): string =
  let open Cbvtype in
  let cycle_nodes =
    let cycles = dfs_cycles ty |> List.map ~f:repr_id in
    List.fold cycles ~init:Int.Set.empty ~f:Int.Set.add in
  let strs = Int.Table.create () in
  let rec str (t: t) l =
    let rec s l =
      match l, case t with
      | `Type, Var
      | `Type, Sgn(Bool _)
      | `Type, Sgn(Nat _) -> s `Atom
      | `Type, Sgn(Pair(c1, (t1, t2))) when concise ->
        Printf.sprintf "%s * %s" (str t1 `Atom) (str t2 `Atom)
      | `Type, Sgn(Pair(c1, (t1, t2))) ->
        Printf.sprintf "%s[%s]%s(%s * %s)" ansi_cyan (string_of_basetype c1)
          ansi_defaultcolor (str t1 `Atom) (str t2 `Atom)
(*      | `Type, Sgn(Fun(c1, (t1, a1, b1, t2))) when concise ->
        Printf.sprintf "%s -> %s" (str t1 `Atom) (str t2 `Type)*)
      | `Type, Sgn(Fun(c1, (t1, a1, b1, t2))) ->
        Printf.sprintf "%s[%s]%s(%s -%s{%s, %s}%s-> %s)"
          ansi_cyan (string_of_basetype c1)
          ansi_defaultcolor (str t1 `Atom)
          ansi_cyan (string_of_basetype a1) (string_of_basetype b1)
          ansi_defaultcolor (str t2 `Type)
      | `Atom, Var -> "\'" ^ (name_of_cbvtypevar t)
      | `Atom, Sgn(Bool _) when concise -> "bool"
      | `Atom, Sgn(Bool c) ->
        Printf.sprintf "bool%s[%s]%s"
          ansi_cyan (string_of_basetype c) ansi_defaultcolor
      | `Atom, Sgn(Nat _) when concise -> "nat"
      | `Atom, Sgn(Nat c) ->
        Printf.sprintf "nat%s[%s]%s"
          ansi_cyan (string_of_basetype c) ansi_defaultcolor
      | `Atom, Sgn(Pair _)
      | `Atom, Sgn(Fun _) ->
        Printf.sprintf "(%s)" (s `Type) in
    let tid = repr_id t in
    match Int.Table.find strs tid with
    | Some s -> s
    | None ->
      if Int.Set.mem cycle_nodes tid then
        let alpha = "''" ^ (name_of_cbvtypevar (newvar())) in
        Int.Table.set strs ~key:tid ~data:alpha;
        let s = "(rec " ^ alpha ^ ". " ^ (s l) ^ ")" in
        Int.Table.set strs ~key:tid ~data:s;
        s
      else
        s l in
  str ty `Type

let rec datatypes_in_basetype (a: Basetype.t) : Ident.Set.t  =
  let open Basetype in
  match case a with
  | Var
  | Sgn(IntB) -> Ident.Set.empty
  | Sgn(BoxB(b)) -> datatypes_in_basetype b
  | Sgn(TupleB(bs)) ->
    Ident.Set.union_list (List.map bs ~f:datatypes_in_basetype)
  | Sgn(DataB(id, params)) ->
    let ds = Ident.Set.union_list (List.map params ~f:datatypes_in_basetype) in
    Ident.Set.add ds id

let rec datatypes_in_cbvtype ?concise:(concise=true)
    (a: Cbvtype.t) : Ident.Set.t =
  let open Cbvtype in
  match case a with
  | Var -> Ident.Set.empty
  | Sgn(Bool _) when concise -> Ident.Set.empty
  | Sgn(Bool c) -> datatypes_in_basetype c
  | Sgn(Nat _) when concise -> Ident.Set.empty
  | Sgn(Nat c) -> datatypes_in_basetype c
  | Sgn(Pair(_, (t1, t2))) when concise ->
    Ident.Set.union (datatypes_in_cbvtype t1) (datatypes_in_cbvtype t2)
  | Sgn(Pair(c1, (t1, t2))) ->
    Ident.Set.union_list
      [datatypes_in_basetype c1; datatypes_in_cbvtype t1; datatypes_in_cbvtype t2]
  | Sgn(Fun(c1, (t1, a1, b1, t2))) ->
    Ident.Set.union_list
      [datatypes_in_basetype c1; datatypes_in_basetype a1;
       datatypes_in_basetype b1; datatypes_in_cbvtype t1;
       datatypes_in_cbvtype t2]

let rec fprint_type ?concise:(concise=true)
    (f: Format.formatter) (x: Ident.t) (a: Cbvtype.t) : unit =
  let open Format in
  fprintf f "@[<hv 1>%s : %s@;" (Ident.to_string x)
    (string_of_cbvtype ~concise:concise a);
  let ds = datatypes_in_cbvtype ~concise:concise a in
  if not (Ident.Set.is_empty ds) then
    begin
      fprintf f "@[<hv 1>where@;";
      Ident.Set.iter ds
        ~f:(fun id -> Format.fprintf f "%s@;" (string_of_data id));
      fprintf f "@]"
    end;
  fprintf f "@]\n"


(** Printing of terms with type annotations *)

let fprint_annotated_term (f: Format.formatter) (term: Cbvterm.t) : unit =
  let open Cbvterm in
  let open Format in
  let rec s_term (t: Cbvterm.t): unit =
    match t.t_desc with
    | Contr(((x, _), xs), t1) ->
      fprintf f "copy %s as %s in@ @["
        (Ident.to_string x)
        (String.concat ~sep:", " (List.map ~f:Ident.to_string xs));
      s_term t1;
      fprintf f "@]"
    | Fun((x, _), t1) ->
      fprintf f "@[<hv 1>\\%s ->@;" (Ident.to_string x);
      s_term t1;
      fprintf f "@]"
    | Fix((_, y, x, a), t1) ->
      fprintf f "@[<hv 1>fix (%s : %s) (%s : %s) ->@;"
        (Ident.to_string y)
        (string_of_cbvtype ~concise:false t.t_type)
        (Ident.to_string x)
        (string_of_cbvtype ~concise:false a);
      s_term t1;
      fprintf f "@]"
    | Tailfix((_, y, x, a), t1) ->
      fprintf f "@[<hv 1>tailfix (%s : %s) (%s : %s) ->@;"
        (Ident.to_string y)
        (string_of_cbvtype ~concise:false t.t_type)
        (Ident.to_string x)
        (string_of_cbvtype ~concise:false a);
      s_term t1;
      fprintf f "@]"
    | If(t1, t2, t3) ->
      fprintf f "@[<hv>if ";
      s_term t1;
      fprintf f " then ";
      s_term t2;
      fprintf f "@ else ";
      s_term t3;
      fprintf f "@]"
    | App(t1, t2) ->
      begin
        match t1.t_desc with
        | Fun((x, _), t1') ->
          fprintf f "@[<hv 1>let %s =@ " (Ident.to_string x);
          s_term t2;
          fprintf f "@] in@ @[";
          s_term t1';
          fprintf f "@]"
        | _ ->
          s_term_inf t
      end
    | Var _ | Const _ | Pair _ | Proj _
      -> s_term_inf t
  and s_term_inf (t: Cbvterm.t) =
    match t.t_desc with
    | Const(Ast.Cinteq, [t1; t2]) ->
      s_term_app t1;
      fprintf f " = ";
      s_term_app t2
    | Const(Ast.Cinteq, _) -> assert false
    | Const(Ast.Cintlt, [t1; t2]) ->
      s_term_app t1;
      fprintf f " < ";
      s_term_app t2
    | Const(Ast.Cintlt, _) -> assert false
    | Const(Ast.Cintadd, [t1; t2]) ->
      s_term_app t1;
      fprintf f " + ";
      s_term_app t2
    | Const(Ast.Cintadd, _) -> assert false
    | Const(Ast.Cintsub, [t1; t2]) ->
      s_term_app t1;
      fprintf f " - ";
      s_term_app t2
    | Const(Ast.Cintsub, _) -> assert false
    | Const(Ast.Cintmul, [t1; t2]) ->
      s_term_app t1;
      fprintf f " * ";
      s_term_app t2
    | Const(Ast.Cintmul, _) -> assert false
    | Const(Ast.Cintdiv, [t1; t2]) ->
      s_term_app t1;
      fprintf f " / ";
      s_term_app t2
    | Const(Ast.Cintdiv, _) -> assert false
    | Fun _ | Fix _ | Tailfix _ | App _ | Var _
    | Const(Ast.Cprint _, _)
    | Const(Ast.Cintprint, _) | Const(Ast.Cintconst _, _)
    | Const(Ast.Cboolconst _, _)
    | Pair _ | Proj _ | Contr _ | If _
      -> s_term_app t
  and s_term_app (t: Cbvterm.t) =
    match t.t_desc with
    | App(t1, t2) ->
      fprintf f "@[";
      s_term_app t1;
      fprintf f "@ ";
      s_term_atom t2;
      fprintf f "@]"
    | _ ->
      s_term_atom t
  and s_term_atom (t: Cbvterm.t) =
    match t.t_desc with
    | Var(x) ->
      fprintf f "%s" (Ident.to_string x)
    | Const(Ast.Cboolconst(true), []) ->
        fprintf f "true"
    | Const(Ast.Cboolconst(false), []) ->
        fprintf f "false"
    | Const(Ast.Cboolconst(_), _) -> assert false
    | Const(Ast.Cintconst(i), []) ->
      if i >= 0 then
        fprintf f "%i" i
      else
        fprintf f "~%i" (-i)
    | Const(Ast.Cintconst _, _) -> assert false
    | Const(Ast.Cprint s, _) ->
      fprintf f "print@ \"%s\"" s
    | Const(Ast.Cintprint, [t1]) ->
      fprintf f "print@ ";
      s_term_atom t1
    | Const(Ast.Cintprint, _) -> assert false
    | Pair(t1, t2) ->
      fprintf f "(@[";
      s_term t1;
      fprintf f "@] ,@ @[";
      s_term t2;
      fprintf f "@])"
    | Proj(t1, i) ->
      fprintf f "@[#%i " (i + 1);
      s_term_atom t1;
      fprintf f "@]"
    | App _ | Fun _ | Fix _ | Tailfix _ | If _ | Contr _
    | Const(Ast.Cinteq, _)
    | Const(Ast.Cintlt, _)
    | Const(Ast.Cintadd, _)
    | Const(Ast.Cintsub, _)
    | Const(Ast.Cintmul, _)
    | Const(Ast.Cintdiv, _) ->
      fprintf f "(@[";
      s_term t;
      fprintf f "@])"
  in
  fprintf f "@[";
  s_term term;
  fprintf f "@]@.\n\n"
