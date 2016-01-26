open Core_kernel.Std
                    
type 'a sgn =  
  | Bool of Basetype.t
  | Nat of Basetype.t
  | Fun of Basetype.t * ('a * Basetype.t * Basetype.t * 'a)
with sexp
    
module Sig = struct

  type 'a t = 'a sgn with sexp                  

  let map (f : 'a -> 'b) (t : 'a t) : 'b t =
    match t with
    | Bool(a) -> Bool(a)
    | Nat(a) -> Nat(a)
    | Fun(c, (x, a, b, y)) -> Fun(c, (f x, a, b, f y))

  let children (t: 'a t) : 'a list =
    match t with
    | Bool _ -> []
    | Nat _ -> []
    | Fun (_, (x, _, _, y)) -> [x; y]

  let equals (s: 'a t) (t: 'a t) ~equals:(eq: 'a -> 'a -> bool) : bool =
    match s, t with
    | Bool(a1), Bool(a2) 
    | Nat(a1), Nat(a2) -> 
       Basetype.equals a1 a2 
    | Fun(c1, (x1, a1, b1, y1)), Fun(c2, (x2, a2, b2, y2)) ->
      Basetype.equals c1 c2 &&
      Basetype.equals a1 a2 &&
      Basetype.equals b1 b2 &&
      eq x1 x2 &&
      eq y1 y2
    | Bool _, _
    | Nat _, _
    | Fun _, _ -> false

  let unify_exn (s: 'a t) (t: 'a t) ~unify:(unify: 'a -> 'a -> unit) : unit =
    match s, t with
    | Bool(a1), Bool(a2) 
    | Nat(a1), Nat(a2) ->
      Basetype.unify_exn a1 a2
    | Fun(c1, (x1, a1, b1, y1)), Fun(c2, (x2, a2, b2, y2)) ->
      Basetype.unify_exn c1 c2; 
      Basetype.unify_exn a1 a2; 
      Basetype.unify_exn b1 b2;
      unify x1 x2;
      unify y1 y2
    | Bool _, _
    | Nat _, _
    | Fun _, _ -> raise Uftype.Constructor_mismatch
end

module Cbvtype = Uftype.Make(Sig)
include Cbvtype

let code (a : Cbvtype.t) : Basetype.t =
  match Cbvtype.case a with
  | Cbvtype.Var -> failwith "code"
  | Cbvtype.Sgn s ->
     match s with
     | Bool _ -> Basetype.boolB
     | Nat _ -> Basetype.newty Basetype.IntB
     | Fun(_, (_, _, d, _)) -> d

let multiplicity (a : Cbvtype.t) : Basetype.t =
  match Cbvtype.case a with
  | Cbvtype.Var -> failwith "multiplicity"
  | Cbvtype.Sgn s ->
    match s with
    | Bool(c)
    | Nat(c) 
    | Fun(c, _) -> c

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

let name_table = Int.Table.create ()
let name_of_typevar t =
  match Int.Table.find name_table (repr_id t) with
  | Some name -> name
  | None ->
    let name = new_name() in
    Int.Table.add_exn name_table ~key:(repr_id t) ~data:name;
    name
  
let to_string ?concise:(concise=true) (ty: t): string =
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
            | Fun(c1, (t1, a1, b1, t2)) ->
              if not concise then
                Printf.sprintf "%s[%s]%s(%s -%s{%s, %s}%s-> %s)"
                  cyan
                  (Printing.string_of_basetype c1)
                  black
                  (str t1 `Atom)
                  cyan
                  (Printing.string_of_basetype a1)
                  (Printing.string_of_basetype b1)
                  black
                  (str t2 `Type)
              else
                Printf.sprintf "%s -> %s" (str t1 `Atom) (str t2 `Type)
        end
      | `Atom ->
        begin
          match case t with
          | Var ->
            "\'" ^ (name_of_typevar t)
          | Sgn st ->
            match st with
            | Bool c ->
              if not concise then
                Printf.sprintf "bool%s[%s]%s"
                  cyan
                  (Printing.string_of_basetype c)
                  black
              else
               "Nat"
            | Nat c ->
              if not concise then
                Printf.sprintf "nat%s[%s]%s"
                  cyan
                  (Printing.string_of_basetype c)
                  black
              else
               "Nat"
            | Fun _ -> Printf.sprintf "(%s)" (s `Type)
        end in
    let tid = repr_id t in
    match Int.Table.find strs tid with
    | Some s -> s
    | None ->
      if Int.Set.mem cycle_nodes tid then
        let alpha = "''" ^ (name_of_typevar (newvar())) in
        Int.Table.replace strs ~key:tid ~data:alpha;
        let s = "(rec " ^ alpha ^ ". " ^ (s l) ^ ")" in
        Int.Table.replace strs ~key:tid ~data:s;
        s
      else
        s l in
  str ty `Type
