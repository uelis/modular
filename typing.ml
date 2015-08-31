(** Type inference *)
open Core.Std

module Ident = Intlib.Ident
module Printing = Intlib.Printing
module Basetype = Intlib.Basetype
module Uftype = Intlib.Uftype
                 
(* Contexts *)
type 'a context = (Ident.t * 'a) list

exception Typing_error of Ast.t option * string

let lhd_constraints = ref []

let eq_constraint t ~expected:expected_ty ~actual:actual_ty =
  try
    Cbvtype.unify_exn expected_ty actual_ty
  with
  | Uftype.Cyclic_type ->
    let msg = "Unification leads to cyclic type." in
    raise (Typing_error(None, msg)) 
  | Uftype.Constructor_mismatch ->
    let msg = Printf.sprintf
                "Term has interactive type %s, but a term of type %s is expected."
                (Cbvtype.to_string actual_ty)
                (Cbvtype.to_string expected_ty) in
    raise (Typing_error(Some t, msg))

let lhd_constraint ~lower:lower_ty ~upper:upper_ty =
  lhd_constraints := (lower_ty, upper_ty) :: !lhd_constraints                        
          
let unitty =
  Basetype.newty Basetype.UnitB
  
let natty () =
  let a = Basetype.newvar() in
  Cbvtype.newty
    (Cbvtype.Nat(a))
  
let funty x y =
  let a = Basetype.newvar() in
  let b = Basetype.newvar() in
  let c = Basetype.newvar() in
  Cbvtype.newty
    (Cbvtype.Fun(c, (x, a, b, y)))

let code_of_type (a : Cbvtype.t) : Basetype.t =
  match Cbvtype.case a with
  | Cbvtype.Var -> failwith "TODO"
  | Cbvtype.Sgn s ->
     match s with
     | Cbvtype.Nat _ -> Basetype.newty Basetype.IntB
     | Cbvtype.Fun(_, (_, _, d, _)) -> d

let code_of_context (gamma: Cbvtype.t context) : Basetype.t =
  List.fold gamma
            ~f:(fun code_gamma (_, c) ->
                let ac = code_of_type c in
                Basetype.newty (Basetype.PairB(code_gamma, ac)))
            ~init:(Basetype.newty Basetype.UnitB)

let rec pt (phi: Cbvtype.t context) (t: Ast.t)
  : Cbvterm.t * (Ident.t * Ident.t) list =
  let open Cbvterm in
  (* Join all instances of x to a single instance of x that appears directly in the term. *)
  let contract x (t1, tinstances) =
    let xs = List.filter_map
               tinstances
               ~f:(fun (y, y') -> if x = y then Some y' else None) in
    let instances = List.filter tinstances ~f:(fun (y, _) -> y <> x) in
    let gamma = List.filter t1.t_context ~f:(fun (y, _) -> not (List.mem xs y)) in
    let a = Cbvtype.newvar () in    
    List.iter t1.t_context
              ~f:(fun (y, b) -> if List.mem xs y then
                                  eq_constraint t ~actual:b ~expected:a);
    { t_desc = Contr((x, xs), t1);
      t_ann = Basetype.newvar ();
      t_type = t1.t_type;
      t_context = (x, a) :: gamma;
      t_loc = t.Ast.loc },
    instances in
  match t.Ast.desc with
  | Ast.Var(v: Ident.t) ->
    let a =
      match List.Assoc.find phi v with
      | Some a -> a
      | None ->
        let msg = "Variable '" ^ (Ident.to_string v) ^ "' not bound." in
        raise (Typing_error (Some t, msg)) in
    let v' = Ident.variant v in
    { t_desc = Cbvterm.Var(v');
      t_ann = Basetype.newvar ();
      t_type = a;
      t_context = [(v', a)];
      t_loc = t.Ast.loc},
    [(v, v')]
  | Ast.Const(Ast.Cintconst _ as c, []) ->
    let a = natty () in
    { t_desc = Const(c, []);
      t_ann = Basetype.newvar ();
      t_type = a;
      t_context = [];
      t_loc = t.Ast.loc},
    []
  | Ast.Const(Ast.Cintprint as c, [s]) ->
     let s1, sinstances = pt phi s in
     eq_constraint s ~actual:s1.t_type ~expected:(natty ());
     { t_desc = Const(c, [s1]);
       t_ann = s1.t_ann;
       t_type = natty ();
       t_context = [];
       t_loc = t.Ast.loc},
     sinstances
  | Ast.Const(Ast.Cintadd as c, [s; t]) ->
     let s1, sinstances = pt phi s in
     let t1, tinstances = pt phi t in
     eq_constraint s ~actual:s1.t_type ~expected:(natty ());
     eq_constraint t ~actual:t1.t_type ~expected:(natty ());
     { t_desc = Const(c, [s1; t1]);
       t_ann = Basetype.newvar ();
       t_type = natty ();
       t_context = s1.t_context @ t1.t_context;
       t_loc = t.Ast.loc },
     sinstances @ tinstances
  | Ast.Const(_) ->
     let msg = "Wrong number of arguments to primitive operation." in
     raise (Typing_error (Some t, msg))
  | Ast.App(s, t) ->
     let s1, sinstances = pt phi s in
     let beta = Cbvtype.newvar () in
     let t1, tinstances = pt phi t in
     eq_constraint s
                   ~actual:s1.t_type
                   ~expected:(funty t1.t_type beta);
     { t_desc = App(s1, t1);
       t_ann = Basetype.newvar ();
       t_type = beta;
       t_context = s1.t_context @ t1.t_context;
       t_loc = t.Ast.loc },
     sinstances @ tinstances
  | Ast.Fun(x, t) ->
     let alpha = Cbvtype.newvar() in
     let t1, tinstances = contract x (pt ((x, alpha)::phi) t) in
     let instances = List.filter tinstances ~f:(fun (y, _) -> y <> x) in
     let gamma = List.filter t1.t_context ~f:(fun (y, _) -> y <> x) in
     { t_desc = Fun((x, alpha), t1);
       t_ann = Basetype.newvar ();
       t_type = funty alpha t1.t_type;
       t_context = gamma;
       t_loc = t.Ast.loc },
     instances
  | Ast.Fix(f, x, s) ->
     let alpha = Cbvtype.newvar() in
     let beta = Cbvtype.newvar() in
     let t1, tinstances = contract x (pt ((f, alpha) :: (x, beta) :: phi) s) in
     let instances = List.filter tinstances ~f:(fun (y, _) -> y <> x && y <> f) in
     let gamma = List.filter t1.t_context ~f:(fun (y, _) -> y <> x && y <> f) in
     let a = funty beta t1.t_type in
     eq_constraint t ~actual:a ~expected:alpha;
     { t_desc = Fix((f, x, beta), t1);
       t_ann = Basetype.newvar ();
       t_type = a;
       t_context = gamma;
       t_loc = t.Ast.loc },
     instances
  | Ast.Ifz(s, tt, tf) ->
     let sa, sinstances = pt phi s in
     let tta, ttinstances = pt phi tt in
     let tfa, tfinstances = pt phi tf in
     eq_constraint s
                   ~actual:sa.t_type
                   ~expected:(natty ());
     eq_constraint tt
                   ~actual:tta.t_type
                   ~expected:(natty ());
     eq_constraint tt
                   ~actual:tfa.t_type
                   ~expected:(natty ());
     { t_desc = Ifz(sa, tta, tfa);
       t_ann = Basetype.newvar ();
       t_type = tta.t_type;
       t_context = sa.t_context @ tta.t_context @ tfa.t_context;
       t_loc = t.Ast.loc },
     sinstances @ ttinstances @ tfinstances

let check_term (phi: Cbvtype.t context) (t: Ast.t)
    : Cbvterm.t =
  let a, _ = pt phi t in
  a
