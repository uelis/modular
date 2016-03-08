open Core_kernel.Std
(** Printing of terms and types *)

let name_counter = ref 0

let new_name () =
  let i = !name_counter in
  incr(name_counter);
  let c = Char.of_int_exn (Char.to_int 'a' + i mod 26) in
  let n = i / 26 in
  if (n = 0) then
    Printf.sprintf "%c" c
  else
    Printf.sprintf "%c%i" c n;;

let reset_names () =
  name_counter := 0

(** Base types *)

let name_base_table = Int.Table.create ()
let name_of_basetypevar t =
  match Int.Table.find name_base_table (Basetype.repr_id t) with
  | Some name -> name
  | None ->
    let name = new_name() in
    Int.Table.add_exn name_base_table
      ~key:(Basetype.repr_id t) ~data:name;
    name

let string_of_basetype (ty: Basetype.t): string =
  let open Basetype in
  let cycle_nodes =
    let cycles = Basetype.dfs_cycles ty |> List.map ~f:Basetype.repr_id in
    List.fold cycles ~init:Int.Set.empty ~f:Int.Set.add in
  let strs = Int.Table.create () in
  let rec str (t: Basetype.t) l =
    let rec s l =
      match l with
      | `Summand ->
        begin
          match case t with
          | Var -> s `Factor
          | Sgn st ->
            begin match st with
            | DataB(id, [t1; t2]) when id = Data.sumid 2 ->
              Printf.sprintf "%s + %s" (str t1 `Summand) (str t2 `Factor)
            | DataB(id, []) when id = Data.sumid 0 -> "void"
            | DataB(id, []) -> id
            | DataB(id, ls) ->
              (*if not (Data.is_discriminated id || Data.is_recursive id) then
                begin
                  let cs = Data.constructor_types id ls in
                  Printf.sprintf "union<%s>"
                    (List.map cs ~f:(fun t2 -> str t2 `Summand)
                     |> String.concat ~sep:", ")
                end
                else*)
                Printf.sprintf "%s<%s>" id
                  (List.map ls ~f:(fun t2 -> str t2 `Summand)
                   |> String.concat ~sep:", ")
            | TupleB _ | IntB | BoxB _ ->
              s `Factor
            end
        end
      | `Factor ->
        begin
          match case t with
          | Var -> s `Atom
          | Sgn st ->
            begin
              match st with
              | TupleB(ts) -> String.concat ~sep:" * "
                                (List.map ~f:(fun t -> str t `Atom) ts)
              | DataB _ | IntB | BoxB _ ->
                s `Atom
            end
        end
      | `Atom ->
        begin
          match case t with
          | Var -> "\'" ^ (name_of_basetypevar t)
          | Sgn st ->
            begin
              match st with
              | IntB -> "int"
              | BoxB(b) -> Printf.sprintf "box<%s>" (str b `Atom)
              | DataB _
              | TupleB []  -> Printf.sprintf "()"
              | TupleB _  -> Printf.sprintf "(%s)" (s `Summand)
            end
        end in
    let tid = repr_id t in
    match Int.Table.find strs tid with
    | Some s -> s
    | None ->
      if Int.Set.mem cycle_nodes tid then
        let alpha = "'" ^ (name_of_basetypevar (newvar())) in
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
  Buffer.add_string buf name;
  if (nparams > 0) then begin
    Buffer.add_string buf "<";
    Buffer.add_string buf (String.concat ~sep:","
                             (List.map ~f:string_of_basetype params));
    Buffer.add_string buf ">";
  end;
  Buffer.add_string buf " = ";
  Buffer.add_string buf
    (String.concat ~sep:" | "
       (List.map ~f:(fun (n, t) ->
          Printf.sprintf "%s of %s" n (string_of_basetype t)) cs));
  Buffer.contents buf

(** cbv types *)

let name_cbv_table = Int.Table.create ()
let name_of_cbvtypevar t =
  match Int.Table.find name_cbv_table (Cbvtype.repr_id t) with
  | Some name -> name
  | None ->
    let name = new_name() in
    Int.Table.add_exn name_cbv_table ~key:(Cbvtype.repr_id t) ~data:name;
    name

let string_of_cbvtype ?concise:(concise=true) (ty: Cbvtype.t): string =
  let open Cbvtype in
  let cyan = "\027[36m" in
  let black = "\027[39m" in
  let cycle_nodes =
    let cycles = dfs_cycles ty |> List.map ~f:repr_id in
    List.fold cycles ~init:Int.Set.empty ~f:Int.Set.add in
  let strs = Int.Table.create () in
  let rec str (t: t) l =
    let rec s l =
      match l with
      | `Type ->
        begin
          match case t with
          | Var -> s `Atom
          | Sgn st ->
            match st with
            | Bool _
            | Nat _ ->
              s `Atom
            | Pair(c1, (t1, t2)) ->
              if not concise then
                Printf.sprintf "%s[%s]%s(%s * %s)"
                  cyan
                  (string_of_basetype c1)
                  black
                  (str t1 `Atom)
                  (str t2 `Atom)
              else
                Printf.sprintf "%s * %s" (str t1 `Atom) (str t2 `Atom)
            | Fun(c1, (t1, a1, b1, t2)) ->
              if not concise then
                Printf.sprintf "%s[%s]%s(%s -%s{%s, %s}%s-> %s)"
                  cyan
                  (string_of_basetype c1)
                  black
                  (str t1 `Atom)
                  cyan
                  (string_of_basetype a1)
                  (string_of_basetype b1)
                  black
                  (str t2 `Type)
              else
                Printf.sprintf "%s -> %s" (str t1 `Atom) (str t2 `Type)
        end
      | `Atom ->
        begin
          match case t with
          | Var ->
            "\'" ^ (name_of_cbvtypevar t)
          | Sgn st ->
            match st with
            | Bool c ->
              if not concise then
                Printf.sprintf "bool%s[%s]%s"
                  cyan
                  (string_of_basetype c)
                  black
              else
               "Nat"
            | Nat c ->
              if not concise then
                Printf.sprintf "nat%s[%s]%s"
                  cyan
                  (string_of_basetype c)
                  black
              else
                "Nat"
            | Pair _
            | Fun _ -> Printf.sprintf "(%s)" (s `Type)
        end in
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
    | Const(Ast.Cboolconst(b), []) ->
      if b then
        fprintf f "true"
      else
        fprintf f "false"
    | Const(Ast.Cboolconst(_), _) -> assert false
    | Const(Ast.Cintconst(i), []) ->
      if i >= 0 then
        fprintf f "%i" i
      else
        fprintf f "~%i" (-i)
    | Const(Ast.Cintconst _, _) -> assert false
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
