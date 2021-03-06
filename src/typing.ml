(** Type inference *)
(* TODO: write down typing invariants *)
open Core_kernel

type 'a context = (Ident.t * 'a) list

type lhd_constraint = {
  lower: Basetype.t;
  upper: Basetype.t;
  reason: string
}

let print_constratint c =
  Printf.printf "  %s <= %s (%s)\n"
    (Printing.string_of_basetype c.lower)
    (Printing.string_of_basetype c.upper)
    c.reason

let solve_constraints (ineqs: lhd_constraint list) : unit =
  let cmp a b = Int.compare
      (Basetype.repr_id a)
      (Basetype.repr_id b) in
  if !Opts.verbose then
    begin
      Printf.printf "Solving constraints:\n";
      List.iter ineqs ~f:print_constratint
    end;
  (* All inequalities have the form A <= alpha for some variable alpha.
   * Gather now all constraints A1 <= alpha, ..., An <= alpha for each
   * variable alpha in the form [A1,...,An] <= alpha. *)
  let joined_lower_bounds =
    ineqs
    |> List.filter ~f:(fun c -> cmp c.lower c.upper <> 0)
    |> List.sort ~compare:(fun c1 c2 -> cmp c1.upper c2.upper)
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
        |> List.dedup_and_sort ~compare:cmp in
      let constraint_recursive =
        List.exists fv_unique ~f:(Basetype.equals alpha) in
      let sol =
        match xs with
        | [] -> assert false
        | [x] when not constraint_recursive -> x
        | xs when not constraint_recursive -> Basetype.sumB xs
        | xs ->
          let cid = Ident.fresh "conty" in
          let params = List.filter fv_unique ~f:(fun beta ->
            not (Basetype.equals beta alpha)) in
          let n = List.length params in
          Basetype.Data.make cid ~param_count:n ~discriminated:false;
          let sol = Basetype.(newty (BoxB (newty (DataB(cid, params))))) in
          (* add constructors *)
          List.iteri xs ~f:(fun i -> fun b ->
            let name = Ident.to_string cid ^ "_" ^ (string_of_int i) in
            let id = Ident.global name in
            let arg_type = Basetype.subst b (fun beta ->
              if Basetype.equals beta alpha then sol else beta) in
            Basetype.Data.add_constructor cid id params arg_type);
          if !Opts.verbose then
            Printf.printf "Declaring type:\n%s\n"
              (Printing.string_of_data cid);
          sol in
      Basetype.unify_exn alpha sol
    | _ ->
      Printf.printf "%s\n" (Printing.string_of_basetype alpha);
      assert false
  in
  List.iter joined_lower_bounds ~f:solve_ineq;
  if !Opts.verbose then
    begin
      Printf.printf "Solution:\n";
      List.iter ineqs ~f:print_constratint
    end

(** Returns the code type of an annotated context *)
let rec code_of_context (gamma : Cbvtype.t context) : Basetype.t =
  let cs = List.map ~f:(fun (_, a) -> Cbvtype.code a) gamma in
  Basetype.(newty (TupleB cs))

(** Replaces the multiplicity with a fresh type variable *)
let freshen_multiplicity (a : Cbvtype.t) : Cbvtype.t =
  match Cbvtype.case a with
  | Cbvtype.Var -> assert false
  | Cbvtype.Sgn s ->
    let m = Basetype.newvar () in
    match s with
    | Cbvtype.Bool _ -> Cbvtype.(newty (Bool(m)))
    | Cbvtype.Nat _ -> Cbvtype.(newty (Nat(m)))
    | Cbvtype.Pair(_, s) -> Cbvtype.(newty (Pair(m, s)))
    | Cbvtype.Fun(_, s) -> Cbvtype.(newty (Fun(m, s)))

(** Adds annotations to a simple type, thus giving a Cbvtype.t *)
let rec fresh_annotations_type (a: Simpletype.t) : Cbvtype.t =
  match Simpletype.case a with
  | Simpletype.Var ->
    let m = Basetype.newvar () in
    Cbvtype.(newty (Nat m))
  | Simpletype.Sgn s ->
    match s with
    | Simpletype.Bool ->
      let m = Basetype.newvar () in
      Cbvtype.(newty (Bool m))
    | Simpletype.Nat ->
      let m = Basetype.newvar () in
      Cbvtype.(newty (Nat m))
    | Simpletype.Pair(x, y) ->
      let xa = fresh_annotations_type x in
      let ya = fresh_annotations_type y in
      let m = Basetype.newvar () in
      Cbvtype.(newty (Pair(m, (xa, ya))))
    | Simpletype.Fun(x, y) ->
      let xa = fresh_annotations_type x in
      let ya = fresh_annotations_type y in
      let m = Basetype.newvar () in
      let d = Basetype.newvar () in
      let a = Basetype.newvar () in
      Cbvtype.(newty (Fun(m, (xa, d, a, ya))))

(** Add fresh type annotations to a term *)
let rec fresh_annotations_term (t: Simpletype.t Cbvterm.term) : Cbvterm.t =
  let open Cbvterm in
  match t.t_desc with
  | Var v ->
    { t_desc = Cbvterm.Var(v);
      t_id = t.t_id;
      t_ann = t.t_ann;
      t_type =  fresh_annotations_type t.t_type;
      t_context = [];
      t_loc = t.t_loc
    }
  | Const(c, ts) ->
    { t_desc = Cbvterm.Const(c, List.map ts ~f:fresh_annotations_term);
      t_id = t.t_id;
      t_ann = t.t_ann;
      t_type =  fresh_annotations_type t.t_type;
      t_context = [];
      t_loc = t.t_loc
    }
  | App(s1, s2) ->
    { t_desc = Cbvterm.App(fresh_annotations_term s1, fresh_annotations_term s2);
      t_id = t.t_id;
      t_ann = t.t_ann;
      t_type =  fresh_annotations_type t.t_type;
      t_context = [];
      t_loc = t.t_loc
    }
  | Pair(s1, s2) ->
    { t_desc = Cbvterm.Pair(fresh_annotations_term s1, fresh_annotations_term s2);
      t_id = t.t_id;
      t_ann = t.t_ann;
      t_type =  fresh_annotations_type t.t_type;
      t_context = [];
      t_loc = t.t_loc
    }
  | Proj(s1, i) ->
    { t_desc = Cbvterm.Proj(fresh_annotations_term s1, i);
      t_id = t.t_id;
      t_ann = t.t_ann;
      t_type =  fresh_annotations_type t.t_type;
      t_context = [];
      t_loc = t.t_loc
    }
  | Fun((x, a), s) ->
    { t_desc = Cbvterm.Fun((x, fresh_annotations_type a),
                           fresh_annotations_term s);
      t_id = t.t_id;
      t_ann = t.t_ann;
      t_type =  fresh_annotations_type t.t_type;
      t_context = [];
      t_loc = t.t_loc
    }
  | If(sc, st, sf) ->
    { t_desc = Cbvterm.If(fresh_annotations_term sc,
                           fresh_annotations_term st,
                           fresh_annotations_term sf);
      t_id = t.t_id;
      t_ann = t.t_ann;
      t_type =  fresh_annotations_type t.t_type;
      t_context = [];
      t_loc = t.t_loc
    }
  | Fix((_, f, x, a), s) ->
    { t_desc = Cbvterm.Fix((Basetype.newvar (), f, x, fresh_annotations_type a),
                           fresh_annotations_term s);
      t_id = t.t_id;
      t_ann = t.t_ann;
      t_type =  fresh_annotations_type t.t_type;
      t_context = [];
      t_loc = t.t_loc
    }
  | Tailfix((_, f, x, a), s) ->
    { t_desc = Cbvterm.Tailfix((Basetype.newvar (), f, x, fresh_annotations_type a),
                               fresh_annotations_term s);
      t_id = t.t_id;
      t_ann = t.t_ann;
      t_type =  fresh_annotations_type t.t_type;
      t_context = [];
      t_loc = t.t_loc
    }
  | Contr(((x, a), xs), s) ->
    { t_desc = Cbvterm.Contr(((x, fresh_annotations_type a), xs),
                             fresh_annotations_term s);
      t_id = t.t_id;
      t_ann = t.t_ann;
      t_type =  fresh_annotations_type t.t_type;
      t_context = [];
      t_loc = t.t_loc
    }

(** Given a term with fresh type variables as annotations,
    infer concrete annotations *)
let infer_annotations (t: Cbvterm.t) : Cbvterm.t =
  let rec constraints (t: Cbvterm.t) : Cbvterm.t * lhd_constraint list =
    let open Cbvterm in
    match t.t_desc with
    | Var v ->
      { t with
        t_context = [(v, t.t_type)]
      },
      []
    | Const(Ast.Cprint _, []) ->
      t,
      []
    | Const(Ast.Cintconst _, []) ->
      t,
      []
    | Const(Ast.Cboolconst _, []) ->
      t,
      []
    | Const(Ast.Cinteq as c, [s1; s2])
    | Const(Ast.Cintlt as c, [s1; s2])
    | Const(Ast.Cintadd as c, [s1; s2])
    | Const(Ast.Cintsub as c, [s1; s2])
    | Const(Ast.Cintmul as c, [s1; s2])
    | Const(Ast.Cintdiv as c, [s1; s2]) ->
      let as1, cs1 = constraints s1 in
      let as2, cs2 = constraints s2 in
      { t with
        t_desc = Const(c, [as1; as2]);
        t_context = as1.t_context @ as2.t_context
      },
      [ { lower = Basetype.(newty (TupleB [t.t_ann; code_of_context as2.t_context]));
          upper = s1.t_ann;
          reason = "prim: stack first"
        };
        (* Note: this condition gives more slack!
             Example: \f -> intadd(f 1, f 3)
        *)
        { lower = Basetype.(newty (TupleB [t.t_ann; intB]));
          upper = s2.t_ann;
          reason = "prim: stack second"
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
    | Const(Ast.Cprint _, _)
    | Const(Ast.Cintconst _, _)
    | Const(Ast.Cboolconst _, _)
    | Const(Ast.Cinteq, _)
    | Const(Ast.Cintlt, _)
    | Const(Ast.Cintadd, _)
    | Const(Ast.Cintsub, _)
    | Const(Ast.Cintmul, _)
    | Const(Ast.Cintdiv, _)
    | Const(Ast.Cintprint, _) ->
      assert false
    | Pair(s1, s2) ->
      let as1, cs1 = constraints s1 in
      let as2, cs2 = constraints s2 in
      let (a, (x, y)) = Cbvtype.unPair t.t_type in
      Cbvtype.unify_exn x (freshen_multiplicity s1.t_type);
      Cbvtype.unify_exn y (freshen_multiplicity s2.t_type);
      { t with
        t_desc = Pair(as1, as2);
        t_context = as1.t_context @ as2.t_context
      },
      [ { lower = Basetype.(newty (TupleB [t.t_ann; code_of_context as2.t_context]));
          upper = s1.t_ann;
          reason = "pair: eval first stack"
        }
      ; { lower = Basetype.(newty (TupleB [t.t_ann; Cbvtype.code as1.t_type]));
          upper = s2.t_ann;
          reason = "pair: eval second stack"
        }
      ; { lower = Basetype.(newty (TupleB [a; Cbvtype.multiplicity x]));
          upper = Cbvtype.multiplicity s1.t_type ;
          reason = "pair: multiplicity left"
        }
      ; { lower = Basetype.(newty (TupleB [a; Cbvtype.multiplicity y]));
          upper = Cbvtype.multiplicity s2.t_type;
          reason = "pair: multiplicity right"
        }
      ] @ cs1 @ cs2
    | Proj(s1, i) ->
      let as1, cs1 = constraints s1 in
      let (a, (x0, x1)) = Cbvtype.unPair s1.t_type in
      let xi = List.nth_exn [x0; x1] i in
      Cbvtype.unify_exn xi t.t_type;
      Basetype.unify_exn t.t_ann s1.t_ann;
      { t with
        t_desc = Proj(as1, i);
        t_context = as1.t_context
      },
      [ { lower = Basetype.unitB;
          upper = a;
          reason = "proj: one pair copy"
        }
      ] @ cs1
    | App(s1, s2) ->
      let as1, cs1 = constraints s1 in
      let as2, cs2 = constraints s2 in
      let c, (x, a, d, y) = Cbvtype.unFun s1.t_type in
      Cbvtype.unify_exn x s2.t_type;
      Cbvtype.unify_exn y t.t_type;
      { t with
        t_desc = App(as1, as2);
        t_context = as1.t_context @ as2.t_context
      },
      [ { lower = Basetype.(newty (TupleB [t.t_ann; code_of_context as2.t_context]));
          upper = s1.t_ann;
          reason = "app: function stack"
        }
      ; { lower = t.t_ann;
          upper = a;
          reason = "app: fun stack"
        }
      ; { lower = Basetype.(newty (TupleB [t.t_ann; d]));
          upper = s2.t_ann;
          reason = "app: argument stack"
        }
      ; { lower = Basetype.unitB;
          upper = c;
          reason = "app: one function copy"
        }
      ]
      @ cs1 @ cs2
    | Fun((v, xa), s) ->
      let as1, cs1 = constraints s in
      let e, (x, a, d, y) = Cbvtype.unFun t.t_type in
      (* note: the bound variable cannot appear in t.t_context *)
      Cbvtype.unify_exn x xa;
      Cbvtype.unify_exn x (List.Assoc.find_exn as1.t_context v ~equal:(=));
      Cbvtype.unify_exn y s.t_type;
      Basetype.unify_exn a s.t_ann;
      let outer_context =
        List.filter_map as1.t_context
          ~f:(fun (y, a) ->
              if y = v then None else Some (y, freshen_multiplicity a)) in
      let context_cs =
        List.map outer_context
          ~f:(fun (y, a) ->
              let a' = List.Assoc.find_exn as1.t_context y ~equal:(=) in
              let m' = Cbvtype.multiplicity a' in
              Cbvtype.unify_exn a (freshen_multiplicity a');
              { lower = Basetype.(newty (TupleB [e; m']));
                upper = Cbvtype.multiplicity a;
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
    | If(sc, st, sf) ->
      let asc, csc = constraints sc in
      let ast, cst = constraints st in
      let asf, csf = constraints sf in
      Basetype.unify_exn st.t_ann t.t_ann;
      Basetype.unify_exn sf.t_ann t.t_ann;
      let rec join
          (t1: Cbvtype.t)
          (t2: Cbvtype.t)
        : Cbvtype.t * lhd_constraint list =
        match Cbvtype.case t1, Cbvtype.case t2 with
        | Cbvtype.Sgn (Cbvtype.Bool _), Cbvtype.Sgn (Cbvtype.Bool _) ->
          Cbvtype.(newty (Bool (Basetype.newvar ()))),
          []
        | Cbvtype.Sgn (Cbvtype.Nat _), Cbvtype.Sgn (Cbvtype.Nat _) ->
          Cbvtype.(newty (Nat (Basetype.newvar ()))),
          []
        | Cbvtype.Sgn (Cbvtype.Pair (m1, (x1, y1))),
          Cbvtype.Sgn (Cbvtype.Pair (m2, (x2, y2))) ->
          Basetype.unify_exn m1 m2; (* TODO ?? *)
          let x, csx = join x1 x2 in
          let y, csy = join y1 y2 in
          Cbvtype.(newty (Pair (m1, (x, y)))),
          csx @ csy
        | Cbvtype.Sgn (Cbvtype.Fun (m1, (x1, c1, d1, y1))),
          Cbvtype.Sgn (Cbvtype.Fun (m2, (x2, c2, d2, y2))) ->
          Basetype.unify_exn m1 m2; (* TODO ?? *)
          Basetype.unify_exn c1 c2; (* TODO ?? *)
          Cbvtype.unify_exn x1 (freshen_multiplicity x2);
          let x = freshen_multiplicity x1 in
          let d = Basetype.newvar () in
          let y, csy = join y1 y2 in
          Cbvtype.(newty (Fun (m1, (x, c1, d, y)))),
          [ { lower = Basetype.sumB [d1; d2];
              upper = d;
              reason = "if: join closure"
            };
            { lower = Basetype.sumB
                  [Cbvtype.multiplicity x1; Cbvtype.multiplicity x2];
              upper = Cbvtype.multiplicity x;
              reason = "if: join argument multiplicity"
            }
          ] @ csy
        | Cbvtype.Var, _
        | Cbvtype.Sgn (Cbvtype.Bool _), _
        | Cbvtype.Sgn (Cbvtype.Nat _), _
        | Cbvtype.Sgn (Cbvtype.Pair _), _
        | Cbvtype.Sgn (Cbvtype.Fun _), _ ->
          assert false in
      let y, csy = join st.t_type sf.t_type in
      Cbvtype.unify_exn t.t_type y;
      { t with
        t_desc = If(asc, ast, asf);
        t_context = asc.t_context @ ast.t_context @ asf.t_context
      },
      [ { lower = Basetype.(newty (TupleB [t.t_ann;
                                           code_of_context ast.t_context;
                                           code_of_context asf.t_context]));
          upper = sc.t_ann;
          reason = "if: condition stack"
        }
      ]
      @ csc @ cst @ csf @ csy
    | Fix((h, f, v, va), s) ->
      let as1, cs1 = constraints s in
      let e, (x, a, d, y) = Cbvtype.unFun t.t_type in
      let g, (x', a', d', y') = Cbvtype.unFun (List.Assoc.find_exn ~equal:(=) as1.t_context f) in
      Basetype.unify_exn a a';
      Basetype.unify_exn d d';
      Cbvtype.unify_exn x x';
      Cbvtype.unify_exn x va;
      Cbvtype.unify_exn x (List.Assoc.find_exn ~equal:(=) as1.t_context v);
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
              let a' = List.Assoc.find_exn ~equal:(=) as1.t_context y in
              let m' = Cbvtype.multiplicity a' in
              Cbvtype.unify_exn a (freshen_multiplicity a');
              { lower = Basetype.(newty (TupleB [h; m']));
                upper = Cbvtype.multiplicity a;
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
      ; { lower = Basetype.(newty (DataB(Data.sumid 2,
                                         [e; newty (TupleB [h; g])])));
          upper = h;
          reason = "fix: call stack"
        }
      ]
      @ cs1 @ context_cs
    | Tailfix((h, f, v, va), s) ->
      (* TODO: verify tail position and that x and y are first-order types. *)
      let as1, cs1 = constraints s in
      let e, (x, a, d, y) = Cbvtype.unFun t.t_type in
      let g, (x', _, d', y') = Cbvtype.unFun (List.Assoc.find_exn ~equal:(=) as1.t_context f) in
      Basetype.unify_exn d d';
      Cbvtype.unify_exn x x';
      Cbvtype.unify_exn x va;
      Cbvtype.unify_exn x (List.Assoc.find_exn ~equal:(=) as1.t_context v);
      Cbvtype.unify_exn y y';
      Cbvtype.unify_exn y s.t_type;
      Basetype.unify_exn as1.t_ann (Basetype.unitB);
      let outer_context =
        List.filter_map as1.t_context
          ~f:(fun (y, a) ->
              if y = v || y = f then None else Some (y, freshen_multiplicity a)) in
      let context_cs =
        List.map outer_context
          ~f:(fun (y, a) ->
              let a' = List.Assoc.find_exn ~equal:(=) as1.t_context y in
              let m' = Cbvtype.multiplicity a' in
              Cbvtype.unify_exn a (freshen_multiplicity a');
              { lower = Basetype.(newty (TupleB [h; m']));
                upper = Cbvtype.multiplicity a;
                reason =
                  Printf.sprintf "tailfix: context (%s)" (Ident.to_string v)
              }) in
      { t with
        t_desc = Tailfix((h, f, v, va), as1);
        t_context = outer_context
      },
      [ { lower = code_of_context outer_context;
          upper = d;
          reason = "tailfix: closure"
        }
      ; { lower =  Basetype.(newty (TupleB [e; a]));
          upper = h;
          reason = "tailfix: eval stack"
        }
      ]
      @ cs1 @ context_cs
    | Contr(((x, a), [y]), s) ->
      let as1, cs1 = constraints s in
      let yt = List.Assoc.find_exn ~equal:(=) as1.t_context y in
      let gamma = List.Assoc.remove as1.t_context y ~equal:(=) in
      Cbvtype.unify_exn t.t_type s.t_type;
      Basetype.unify_exn t.t_ann s.t_ann;
      Cbvtype.unify_exn a yt;
      { t with
        t_desc = Contr(((x, a), [y]), as1);
        t_context = (x, a) :: gamma
      },
      cs1
    | Contr(((x, a), xs), s) ->
      let as1, cs1 = constraints s in
      let m = Cbvtype.multiplicity a in
      let delta, gamma =
        List.partition_tf as1.t_context ~f:(fun (y, _) -> List.mem ~equal:(=) xs y) in
      let sum =
        let ms = List.map delta ~f:(fun (_, a) -> Cbvtype.multiplicity a) in
        let n = List.length ms in
        Basetype.(newty (DataB(Data.sumid n, ms))) in
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

let check_term (t: Ast.t) : Cbvterm.t =
  let lt = Simpletyping.check t in
  assert (lt.Simpletyping.subst = []);
  let lt1 = fresh_annotations_term lt.Simpletyping.linear_term in
  infer_annotations lt1
