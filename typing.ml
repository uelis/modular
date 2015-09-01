(** Type inference *)
open Core.Std

module Ident = Intlib.Ident
module Printing = Intlib.Printing
module Basetype = Intlib.Basetype
module Uftype = Intlib.Uftype
                 
(* Contexts *)
type 'a context = (Ident.t * 'a) list

exception Typing_error of Ast.t option * string

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

let selectfunty x =
  match Cbvtype.case x with
  | Cbvtype.Sgn (Cbvtype.Fun(c, x)) -> (c, x)
  | _ -> failwith "unfunty"
                  
let freshen_multiplicity (a : Cbvtype.t) : Cbvtype.t =
  match Cbvtype.case a with
  | Cbvtype.Var -> a
  | Cbvtype.Sgn s ->
     let m = Basetype.newvar () in
     match s with
     | Cbvtype.Nat _ -> Cbvtype.newty (Cbvtype.Nat(m))
     | Cbvtype.Fun(_, s) -> Cbvtype.newty (Cbvtype.Fun(m, s))

let rec pt (phi: Cbvtype.t context) (t: Ast.t)
  : Cbvterm.t * (Ident.t * Ident.t) list =
  let open Cbvterm in
  (* Join all instances of x to a single instance of x that appears directly in the term. *)
  let contract_instances x (t1, tinstances) =
    let xs = List.filter_map
               tinstances
               ~f:(fun (y, y') -> if x = y then Some y' else None) in
    let instances = List.filter tinstances ~f:(fun (y, _) -> y <> x) in
    let gamma = List.filter t1.t_context ~f:(fun (y, _) -> not (List.mem xs y)) in
    let a0 = Cbvtype.newvar () in    
    List.iter t1.t_context
              ~f:(fun (y, b) -> if List.mem xs y then
                                  eq_constraint t ~actual:b ~expected:a0);
    let a = freshen_multiplicity a0 in
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
     let t1, tinstances = contract_instances x (pt ((x, alpha)::phi) t) in
     let instances = List.filter tinstances ~f:(fun (y, _) -> y <> x) in
     let gamma0 = List.filter t1.t_context ~f:(fun (y, _) -> y <> x) in
     let gamma = List.map ~f:(fun (y,a) -> (y, freshen_multiplicity a)) gamma0 in
     { t_desc = Fun((x, alpha), t1);
       t_ann = Basetype.newvar ();
       t_type = funty alpha t1.t_type;
       t_context = gamma;
       t_loc = t.Ast.loc },
     instances
  | Ast.Fix(f, x, s) ->
     let alpha = Cbvtype.newvar() in
     let beta = Cbvtype.newvar() in
     let t1, tinstances = contract_instances f (contract_instances x (pt ((f, alpha) :: (x, beta) :: phi) s)) in
     let instances = List.filter tinstances ~f:(fun (y, _) -> y <> x && y <> f) in
     let gamma0 = List.filter t1.t_context ~f:(fun (y, _) -> y <> x && y <> f) in
     let gamma = List.map ~f:(fun (y,a) -> (y, freshen_multiplicity a)) gamma0 in
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

type lhd_constraint = {
    lower: Basetype.t;
    upper: Basetype.t;
    reason: string
  }
                        
let solve_constraints (ineqs: lhd_constraint list) : unit =
  let cmp a b = Int.compare
                  (Basetype.repr_id a)
                  (Basetype.repr_id b) in
  if true then
    begin
      Printf.printf "Solving constraints:\n";
      List.iter ineqs
        ~f:(fun c -> Printf.printf "  %s <= %s (%s)\n"
                       (Printing.string_of_basetype c.lower)
                       (Printing.string_of_basetype c.upper)
                       c.reason
           )
    end;
  (* Turn all encoding type upper bounds into type variables. *)
  List.iter ineqs
    ~f:(fun c -> 
      match Basetype.case c.upper with
      | Basetype.Sgn (Basetype.EncodedB alpha) -> 
        Basetype.replace_by c.upper alpha
      | _ -> ());
  (* All inequalities have the form A <= alpha for some variable alpha.
   * Gather now all constraints A1 <= alpha, ..., An <= alpha for each
   * variable alpha in the form [A1,...,An] <= alpha. *)
  let joined_lower_bounds =
    ineqs
    |> List.sort ~cmp:(fun c1 c2 -> cmp c1.upper c2.upper)
    |> List.group ~break:(fun c1 c2 -> cmp c1.upper c2.upper <> 0)
    |> List.map
         ~f:(function
           | [] -> assert false
           | c :: rest ->
             (* lower bounds *)
             let bs = List.map (c :: rest) ~f:(fun c -> c.lower) in
             (* remove duplicates *)
             let rec dedup_quadratic bs =
               match bs with
               | [] -> []
               | b :: rest ->
                 let dedup_rest = dedup_quadratic rest in
                 if List.mem ~equal:Basetype.equals dedup_rest b
                 then dedup_rest
                 else b :: dedup_rest in
             let bs_dedup = dedup_quadratic bs in
             (bs_dedup, c.upper)) in
  let solve_ineq (xs, alpha) =
    match Basetype.case alpha with
    | Basetype.Var ->
      let fv_unique =
        List.map xs ~f:Basetype.free_vars
        |> List.concat
        |> List.dedup ~compare:cmp in
      let constraint_recursive =
        List.exists fv_unique ~f:(Basetype.equals alpha) in
      let sol =
        if List.length xs > 1 || constraint_recursive then
          begin
            let recty = Basetype.Data.fresh_id "conty" in
            let params = List.filter fv_unique
                           ~f:(fun beta -> not (Basetype.equals beta alpha)) in
            let n = List.length params in
            Basetype.Data.make recty ~nparams:n ~discriminated:false;
            let data = Basetype.newty (Basetype.DataB(recty, params)) in
            let sol =
              if constraint_recursive then
                Basetype.newty (Basetype.BoxB(data))
              else data in
            (* add constructors *)
            List.iteri xs
              ~f:(fun i -> fun b ->
                let arg_type =
                  Basetype.subst b
                    (fun beta ->
                       if Basetype.equals beta alpha then sol else beta)
                    in
                Basetype.Data.add_constructor
                  recty
                  (recty ^ "_" ^ (string_of_int i))
                  params
                  arg_type);
            if true then
              Printf.printf "Declaring type:\n  %s\n" (Printing.string_of_data recty);
            sol
          end
        else
          (assert (xs <> []);
           List.hd_exn xs) in
      Basetype.unify_exn alpha sol
    | _ ->
      Printf.printf "%s\n" (Printing.string_of_basetype alpha);
      assert false
  in
  List.iter joined_lower_bounds ~f:solve_ineq
          
let code_of_type (a : Cbvtype.t) : Basetype.t =
  match Cbvtype.case a with
  | Cbvtype.Var -> Basetype.newty Basetype.UnitB (* ??? *)
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
            
let multiplicity_of_type (a : Cbvtype.t) : Basetype.t =
  match Cbvtype.case a with
  | Cbvtype.Var -> Basetype.newvar()
  | Cbvtype.Sgn s ->
     match s with
     | Cbvtype.Nat(_) -> Basetype.newvar()
     | Cbvtype.Fun(c, _) -> c

let multiplicities_of_context  (gamma: Cbvtype.t context) : Basetype.t list =
  List.map ~f:(fun (_, a) -> multiplicity_of_type a) gamma 

let infer_annotations (t: Cbvterm.t) : unit =
  let rec constraints (t: Cbvterm.t) : lhd_constraint list =
    let open Cbvterm in
    match t.t_desc with
    | Var _ -> []
    | Const(c, ts) ->
       (* TODO *)
       List.concat_map ts ~f:constraints       
    | App(s1, s2) ->
       let cs1 = constraints s1 in
       let cs2 = constraints s2 in
       let c, (_, a, d, _) = selectfunty s1.t_type in
       [ { lower = Basetype.newty (Basetype.PairB(t.t_ann, code_of_context s2.t_context));
           upper = s1.t_ann;
           reason = "app: function stack"
         }
       ; { lower = Basetype.newty (Basetype.PairB(t.t_ann, d));
           upper = s2.t_ann;
           reason = "app: argument stack"
         }
       ; { lower = Basetype.newty (Basetype.UnitB);
           upper = c;
           reason = "app: one function copy"
         }
       ]
       @ cs1 @ cs2
    | Fun((x,_), s) ->
       let cs = constraints s in
       let e, (_, a, d, _) = selectfunty t.t_type in
       (* note: the bound variable cannot appear in t.t_context *)
       Basetype.unify_exn a s.t_ann;
       let context_cs =
         List.map
           t.t_context
           ~f:(fun (y, a) ->
               let a' = List.Assoc.find_exn s.t_context y in
               { lower = Basetype.newty
                           (Basetype.PairB(e, multiplicity_of_type a'));
                 upper = multiplicity_of_type a;
                 reason =
                   Printf.sprintf "fun: context (%s)" (Ident.to_string x)
               }) in
(*       List.iter t.t_context
                 ~f:(fun (y, a) ->
                     let a' = List.Assoc.find_exn s.t_context y in
                     Basetype.unify_exn
                       (multiplicity_of_type a)
                       (Basetype.newty
                          (Basetype.PairB(e, multiplicity_of_type a'))));
 *)     
       [ { lower = code_of_context s.t_context;
           upper = d;
           reason = "fun: closure"
         }
       ]
       @ context_cs @ cs
    | Ifz(sc, st, sf) ->
       let csc = constraints sc in
       let cst = constraints st in
       let csf = constraints sf in
       [ { lower = Basetype.newty
                     (Basetype.PairB(t.t_ann,
                                     Basetype.newty
                                       (Basetype.PairB(code_of_context st.t_context,
                                                       code_of_context sf.t_context))));
           upper = sc.t_ann;
           reason = "if: condition stack"
         }
       ]
       @ csc @ cst @ csf
    | Fix((f, _, _), s) ->
       let cs = constraints s in
       let g, (_, a, d, _) = selectfunty (List.Assoc.find_exn s.t_context f) in
       let e, (_, a', d', _) = selectfunty (List.Assoc.find_exn s.t_context f) in
       Basetype.unify_exn a a';
       Basetype.unify_exn d d';
       Basetype.unify_exn a s.t_ann;
       let h = Basetype.newvar() in
       List.iter t.t_context
                 ~f:(fun (y, a) ->
                     let a' = List.Assoc.find_exn s.t_context y in
                     Basetype.unify_exn
                       (multiplicity_of_type a)
                       (Basetype.newty
                          (Basetype.PairB(h, multiplicity_of_type a'))));
       [ { lower = code_of_context t.t_context;
           upper = d;
           reason = "fix: closure"
         }
       ; { lower = Basetype.newty
                     (Basetype.DataB(Basetype.Data.sumid 2,
                                     [e; Basetype.newty (Basetype.PairB(h, g))]));
           upper = h;
           reason = "fix: call stack"
         }
       ]
       @ cs
    | Contr((x, xs), s) ->
       let cs = constraints s in
       let m = multiplicity_of_type (List.Assoc.find_exn t.t_context x) in
       let ms = List.map
                  ~f:(fun (y, a) -> multiplicity_of_type a)
                  (List.filter
                     ~f:(fun (y, _) -> List.mem xs y)
                     s.t_context) in
       let n = List.length ms in
       let sum =
         match ms with
         | [] -> Basetype.newty Basetype.UnitB
         | [m'] -> m'
         | _ -> 
            Basetype.newty
              (Basetype.DataB(Basetype.Data.sumid n, ms)) in
       (*       Basetype.unify_exn m sum; *)
       [ { lower = sum;
           upper = m;
           reason = "contraction"
         }
       ]
       @ cs in
  let cs = constraints t in
  solve_constraints cs

let check_term (phi: Cbvtype.t context) (t: Ast.t)
    : Cbvterm.t =
  let t1, _ = pt phi t in
  infer_annotations t1;
  t1
