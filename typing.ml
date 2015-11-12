(** Type inference *)
open Core_kernel.Std

type 'a context = (Ident.t * 'a) list

let selectfunty a =
  match Cbvtype.case a with
  | Cbvtype.Sgn (Cbvtype.Fun(m, x)) -> m, x
  | _ -> assert false

type lhd_constraint = {
  lower: Basetype.t;
  upper: Basetype.t;
  reason: string
}

let solve_constraints (ineqs: lhd_constraint list) : unit =
  let cmp a b = Int.compare
      (Basetype.repr_id a)
      (Basetype.repr_id b) in
  if !Opts.verbose then
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
            Basetype.Data.make recty ~param_count:n ~discriminated:false;
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

let rec code_of_context (gamma : Cbvtype.t context) : Basetype.t =
  match gamma with
  | [] -> Basetype.newty Basetype.UnitB
  | (_, a) :: delta ->
    Basetype.newty (Basetype.PairB(code_of_context delta, Cbvtype.code a))

let multiplicity_of_type (a : Cbvtype.t) : Basetype.t =
  match Cbvtype.case a with
  | Cbvtype.Var -> Basetype.newvar()
  | Cbvtype.Sgn s ->
    match s with
    | Cbvtype.Nat(c) -> c
    | Cbvtype.Fun(c, _) -> c

let multiplicities_of_context  (gamma: Cbvtype.t context) : Basetype.t list =
  List.map ~f:(fun (_, a) -> multiplicity_of_type a) gamma 

let freshen_multiplicity (a : Cbvtype.t) : Cbvtype.t =
  match Cbvtype.case a with
  | Cbvtype.Var -> assert false
  | Cbvtype.Sgn s ->
    let m = Basetype.newvar () in
    match s with
    | Cbvtype.Nat _ -> Cbvtype.newty (Cbvtype.Nat(m))
    | Cbvtype.Fun(_, s) -> Cbvtype.newty (Cbvtype.Fun(m, s))

let rec fresh_annotations_type (a: Simpletype.t) : Cbvtype.t =
  match Simpletype.case a with
  | Simpletype.Var ->
    let m = Basetype.newvar () in
    Cbvtype.newty (Cbvtype.Nat m)
  | Simpletype.Sgn s ->
    match s with
    | Simpletype.Nat -> 
      let m = Basetype.newvar () in
      Cbvtype.newty (Cbvtype.Nat m)
    | Simpletype.Fun(x, y) ->
      let xa = fresh_annotations_type x in
      let ya = fresh_annotations_type y in
      let m = Basetype.newvar () in
      let d = Basetype.newvar () in
      let a = Basetype.newvar () in
      Cbvtype.newty (Cbvtype.Fun(m, (xa, d, a, ya)))

let fresh_annotations_context (t: Simpletype.t context)
  : Cbvtype.t context =
  List.map t ~f:(fun (x, a) -> (x, fresh_annotations_type a))

let rec fresh_annotations_term (t: Simpletype.t Cbvterm.term) : Cbvterm.t =
  let open Cbvterm in
  match t.t_desc with
  | Var v ->
    { t_desc = Cbvterm.Var(v);
      t_ann = t.t_ann;
      t_type =  fresh_annotations_type t.t_type;
      t_context = [];
      t_loc = t.t_loc
    }
  | Const(c, ts) ->
    { t_desc = Cbvterm.Const(c, List.map ts ~f:fresh_annotations_term);
      t_ann = t.t_ann;
      t_type =  fresh_annotations_type t.t_type;
      t_context = [];
      t_loc = t.t_loc
    }
  | App(s1, s2) ->
    { t_desc = Cbvterm.App(fresh_annotations_term s1, fresh_annotations_term s2);
      t_ann = t.t_ann;
      t_type =  fresh_annotations_type t.t_type;
      t_context = [];
      t_loc = t.t_loc
    }
  | Fun((x, a), s) ->
    { t_desc = Cbvterm.Fun((x, fresh_annotations_type a),
                           fresh_annotations_term s);
      t_ann = t.t_ann;
      t_type =  fresh_annotations_type t.t_type;
      t_context = [];
      t_loc = t.t_loc
    }
  | Ifz(sc, st, sf) ->
    { t_desc = Cbvterm.Ifz(fresh_annotations_term sc,
                           fresh_annotations_term st,
                           fresh_annotations_term sf);
      t_ann = t.t_ann;
      t_type =  fresh_annotations_type t.t_type;
      t_context = [];
      t_loc = t.t_loc
    }
  | Fix((_, f, x, a), s) ->
    { t_desc = Cbvterm.Fix((Basetype.newvar (), f, x, fresh_annotations_type a),
                           fresh_annotations_term s);
      t_ann = t.t_ann;
      t_type =  fresh_annotations_type t.t_type;
      t_context = [];
      t_loc = t.t_loc
    }
  | Contr(((x, a), xs), s) ->
    { t_desc = Cbvterm.Contr(((x, fresh_annotations_type a), xs),
                             fresh_annotations_term s);
      t_ann = t.t_ann;
      t_type =  fresh_annotations_type t.t_type;
      t_context = [];
      t_loc = t.t_loc
    }

let infer_annotations (t: Cbvterm.t) : Cbvterm.t =
  let rec constraints (t: Cbvterm.t) : Cbvterm.t * lhd_constraint list =
    let open Cbvterm in
    match t.t_desc with
    | Var v ->
      { t with
        t_context = [(v, t.t_type)]
      },
      []
    | Const(Ast.Cintconst _, []) ->
      t,
      []
    | Const(Ast.Cintadd, [s1; s2]) ->
      let as1, cs1 = constraints s1 in
      let as2, cs2 = constraints s2 in
      { t with
        t_desc = Const(Ast.Cintadd, [as1; as2]);
        t_context = as1.t_context @ as2.t_context
      },
      [ { lower = Basetype.newty (Basetype.PairB(t.t_ann, code_of_context as2.t_context));
          upper = s1.t_ann;
          reason = "add: stack first"
        };
        (* Note: this condition gives more slack!
             Example: \f -> intadd(f 1, f 3)
        *)              
        { lower = Basetype.newty (Basetype.PairB(t.t_ann, Basetype.newty Basetype.IntB));
          upper = s2.t_ann;
          reason = "add: stack second"
        }
      ] @ cs1 @ cs2
    | Const(Ast.Cintprint, [s1]) ->
      let as1, cs1 = constraints s1 in
      Cbvtype.unify_exn t.t_type s1.t_type;
      Basetype.unify_exn t.t_ann s1.t_ann;
      { t with
        t_desc = Const(Ast.Cintprint, [as1]);
        t_context = as1.t_context
      },
      cs1
    | Const _ ->
      assert false
    | App(s1, s2) ->
      let as1, cs1 = constraints s1 in
      let as2, cs2 = constraints s2 in
      let c, (x, a, d, y) = selectfunty s1.t_type in
      Cbvtype.unify_exn x s2.t_type;
      Cbvtype.unify_exn y t.t_type;
      { t with
        t_desc = App(as1, as2);
        t_context = as1.t_context @ as2.t_context
      },
      [ { lower = Basetype.newty (Basetype.PairB(t.t_ann, code_of_context as2.t_context));
          upper = s1.t_ann;
          reason = "app: function stack"
        }
      ; { lower = t.t_ann;
          upper = a;
          reason = "app: fun stack"
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
    | Fun((v, xa), s) ->
      let as1, cs1 = constraints s in
      let e, (x, a, d, y) = selectfunty t.t_type in
      (* note: the bound variable cannot appear in t.t_context *)
      Cbvtype.unify_exn x xa;
      Cbvtype.unify_exn x (List.Assoc.find_exn as1.t_context v);
      Cbvtype.unify_exn y s.t_type;
      Basetype.unify_exn a s.t_ann;
      let outer_context =
        List.filter_map as1.t_context
          ~f:(fun (y, a) ->
              if y = v then None else Some (y, freshen_multiplicity a)) in
      let context_cs =
        List.map outer_context
          ~f:(fun (y, a) ->
              let a' = List.Assoc.find_exn as1.t_context y in
              let m' = multiplicity_of_type a' in
              Cbvtype.unify_exn a (freshen_multiplicity a');
              { lower = Basetype.newty (Basetype.PairB(e, m'));
                upper = multiplicity_of_type a;
                reason =
                  Printf.sprintf "fun: context (%s)" (Ident.to_string v)
              }) in
      { t with
        t_desc = Fun((v, xa), as1);
        t_context = outer_context
      },
      [ { lower = code_of_context outer_context;
          upper = d;
          reason = "fun: closure"
        }
      ]
      @ context_cs @ cs1
    | Ifz(sc, st, sf) ->
      let asc, csc = constraints sc in
      let ast, cst = constraints st in
      let asf, csf = constraints sf in
      Basetype.unify_exn st.t_ann t.t_ann;
      Basetype.unify_exn sf.t_ann t.t_ann;
      let rec join
          (t1: Cbvtype.t)
          (t2: Cbvtype.t)
        : Cbvtype.t * lhd_constraint list =
        let open Cbvtype in
        match case t1, case t2 with
        | Sgn (Nat _), Sgn (Nat _) ->
          newty (Nat (Basetype.newvar ())),
          []
        | Sgn (Fun (m1, (x1, c1, d1, y1))), Sgn (Fun (m2, (x2, c2, d2, y2))) ->
          Basetype.unify_exn m1 m2; (* TODO ?? *)
          Basetype.unify_exn c1 c2; (* TODO ?? *)
          Cbvtype.unify_exn x1 (freshen_multiplicity x2);
          let x = freshen_multiplicity x1 in
          let d = Basetype.newvar () in
          let y, csy = join y1 y2 in
          newty (Fun (m1, (x, c1, d, y))),
          [ { lower = Basetype.newty
                  (Basetype.DataB(Basetype.Data.sumid 2, [d1; d2]));
              upper = d;
              reason = "if: join closure"
            };
            { lower = Basetype.newty
                  (Basetype.DataB(Basetype.Data.sumid 2,
                                  [multiplicity x1; multiplicity x2]));
              upper = multiplicity x;
              reason = "if: join argument multiplicity"
            };
          ] @ csy
        | _, _ -> assert false in
      let y, csy = join st.t_type sf.t_type in
      Cbvtype.unify_exn t.t_type y;
      { t with
        t_desc = Ifz(asc, ast, asf);
        t_context = asc.t_context @ ast.t_context @ asf.t_context
      },
      [ { lower = Basetype.newty
              (Basetype.PairB(t.t_ann,
                              Basetype.newty
                                (Basetype.PairB(code_of_context ast.t_context,
                                                code_of_context asf.t_context))));
          upper = sc.t_ann;
          reason = "if: condition stack"
        }
      ]
      @ csc @ cst @ csf @ csy
    | Fix((h, f, v, va), s) ->
      let as1, cs1 = constraints s in
      let e, (x, a, d, y) = selectfunty t.t_type in
      let g, (x', a', d', y') = selectfunty (List.Assoc.find_exn as1.t_context f) in
      Basetype.unify_exn a a';
      Basetype.unify_exn d d';
      Cbvtype.unify_exn x x';
      Cbvtype.unify_exn x va;
      Cbvtype.unify_exn x (List.Assoc.find_exn as1.t_context v);
      Cbvtype.unify_exn y y';
      Cbvtype.unify_exn y s.t_type;
      Basetype.unify_exn a s.t_ann;
      let outer_context =
        List.filter_map as1.t_context
          ~f:(fun (y, a) ->
              if y = v || y = f then None else Some (y, freshen_multiplicity a)) in
      let context_cs =
        List.map outer_context
          ~f:(fun (y, a) ->
              let a' = List.Assoc.find_exn as1.t_context y in
              let m' =  multiplicity_of_type a' in
              Cbvtype.unify_exn a (freshen_multiplicity a');
              { lower = Basetype.newty (Basetype.PairB(h, m'));
                upper = multiplicity_of_type a;
                reason = Printf.sprintf "fix: context (%s)" (Ident.to_string y)
              }) in
      { t with
        t_desc = Fix((h, f, v, va), as1);
        t_context = outer_context
      },
      [ { lower = code_of_context outer_context;
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
      @ cs1 @ context_cs
    | Contr(((x, a), xs), s) ->
      let as1, cs1 = constraints s in
      let m = multiplicity_of_type a in
      let delta, gamma =
        List.partition_tf as1.t_context ~f:(fun (y, _) -> List.mem xs y) in
      let sum =
        let ms = List.map delta ~f:(fun (y, a) -> multiplicity_of_type a) in
        let n = List.length ms in
        Basetype.newty
          (Basetype.DataB(Basetype.Data.sumid n, ms)) in
      Cbvtype.unify_exn t.t_type s.t_type;
      Basetype.unify_exn t.t_ann s.t_ann;
      List.iter delta
        ~f:(fun (_, b) -> Cbvtype.unify_exn a (freshen_multiplicity b));
      { t with
        t_desc = Contr(((x, a), xs), as1);
        t_context = (x, a) :: gamma
      },
      [ { lower = sum;
          upper = m;
          reason = "contraction"
        }
      ]
      @ cs1 in
  let as1, cs1 = constraints t in
  solve_constraints cs1;
  as1

let check_term (t: Ast.t)
  : Cbvterm.t =
  let lt = Simpletyping.linearize [] t in
  assert (lt.Simpletyping.subst = []);
  let lt1 = fresh_annotations_term lt.Simpletyping.linear_term in
  infer_annotations lt1
