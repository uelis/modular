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
            | PairB _ | EncodedB _ | IntB | ZeroB | UnitB | BoxB _ | ArrayB _ ->
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
              | PairB(t1, t2) -> str t1 `Factor ^ " * " ^ str t2 `Atom
              | DataB _ | EncodedB _ | IntB | ZeroB | UnitB | BoxB _ | ArrayB _ ->
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
              | EncodedB b -> "''" ^ (str b `Atom)
              | IntB -> "int"
              | ZeroB -> "void"
              | UnitB -> "unit"
              | BoxB(b) -> Printf.sprintf "box<%s>" (str b `Atom)
              | ArrayB(b) -> Printf.sprintf "array<%s>" (str b `Atom)
              | DataB _
              | PairB _  -> Printf.sprintf "(%s)" (s `Summand)
            end
        end in
    let tid = repr_id t in
    match Int.Table.find strs tid with
    | Some s -> s
    | None ->
      if Int.Set.mem cycle_nodes tid then
        let alpha = "'" ^ (name_of_basetypevar (newvar())) in
        Int.Table.replace strs ~key:tid ~data:alpha;
        let s = "(rec " ^ alpha ^ ". " ^ (s l) ^ ")" in
        Int.Table.replace strs ~key:tid ~data:s;
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
