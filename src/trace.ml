open Core_kernel.Std
open Ssa

let fresh_var () = Ident.fresh "z"

(**
   Tracing
*)
let trace_block blocks i0 =
  let block = Ident.Table.find_exn blocks i0 in
  let l0 = label_of_block block in
  let x0 = List.map ~f:(fun _ -> fresh_var ()) l0.arg_types in

  (* substitution *)
  let rho = Ident.Table.create () in
  (* current body *)
  let lets = ref [] in
  (* already visited labels *)
  let visited = Ident.Table.create () in

  let rec remove_last_push ls =
    match ls with
    | [] -> None
    | Let(_, Const(Ssa.Cpush(_), v)) :: rest-> Some (v, rest)
    | l :: rest ->
      begin
        match remove_last_push rest with
        | Some (v, ls') -> Some (v, l::ls')
        | None  -> None
      end in
  let trace_let l =
    match l with
    | Let((x, a), t) ->
      let t' = subst_term (Ident.Table.find_exn rho) t in
      begin
        match t', !lets with
        | Val v', _ ->
          Ident.Table.set rho ~key:x ~data:v'
        | Const(Ssa.Cpop(_), _), _ ->
          begin
            match remove_last_push !lets with
            | Some (v', lets') ->
              lets := lets';
              Ident.Table.set rho ~key:x ~data:v'
            | None ->
              let x' = fresh_var () in
              Ident.Table.set rho ~key:x ~data:(Var x');
              lets := Let((x', a), t') :: !lets
          end
        (* quick hack to eliminate Alloc,Store,Load,Free sequences
           immediately *)
          (* TODO:
        | Load(addr1, _), Let((z1, a1), Store(addr2, v, _)) :: rest
          when addr1 = addr2 ->
          String.Table.set rho ~key:x ~data:v;
          lets := rest @ [Let((z1, a1), Val(Unit))]
        | Free(addr1, _), Let((addr2, anat) , Alloc(_)) :: rest
          when addr1 = Var addr2 ->
          String.Table.set rho ~key:x ~data:Unit;
          lets := rest @ [Let((addr2, anat), Val(IntConst(0)))]
          *)
        | _ ->
          let x' = fresh_var () in
          Ident.Table.set rho ~key:x ~data:(Var x');
          lets := Let((x', a), t') :: !lets
      end in
  let trace_lets lets = List.iter (List.rev lets) ~f:trace_let in
  let flush_lets () =
    let ls = !lets in
    lets := [];
    ls in

  (* tracing of blocks*)
  let rec trace_block i vs =
    let block = Ident.Table.find_exn blocks i in
    match Ident.Table.find visited i with
    | Some i when i > !Opts.trace_loop_threshold ->
      let lets = flush_lets () in
      let dst = label_of_block block in
      Direct(l0, x0, lets, vs, dst)
    | _ ->
      begin
        Ident.Table.change visited i (function None -> Some 1
                                             | Some i -> Some (i+1));
        (* Printf.printf "%s\n" (string_of_letbndgs !lets); *)
        match block with
        | Unreachable(_) -> Unreachable(l0)
        | Direct(_, xs, lets, vr, dst) ->
          List.iter2_exn xs vs
            ~f:(fun x v -> Ident.Table.set rho ~key:x ~data:v);
          trace_lets lets;
          let vr' = List.map vr ~f:(subst_value (Ident.Table.find_exn rho)) in
          trace_block dst.name vr'
        | Branch(_, xs, lets, (id, params, vc, cases)) ->
          List.iter2_exn xs vs
            ~f:(fun x v -> Ident.Table.set rho ~key:x ~data:v);
          trace_lets lets;
          let vc' = subst_value (Ident.Table.find_exn rho) vc in
          begin
            match vc' with
            | In((_, i, vi), _) ->
              let (y, vd, dst) = List.nth_exn cases i in
              Ident.Table.set rho ~key:y ~data:vi;
              let vd' = List.map vd ~f:(subst_value (Ident.Table.find_exn rho)) in
              trace_block dst.name vd'
            | _ ->
              let lets = flush_lets () in
              let cases' =
                List.map cases
                  ~f:(fun (y, vd, dst) ->
                    let y' = fresh_var () in
                    Ident.Table.set rho ~key:y ~data:(Var y');
                    let vd' = List.map vd ~f:(subst_value (Ident.Table.find_exn rho)) in
                    (y', vd', dst)) in
              Branch(l0, x0, lets, (id, params, vc', cases'))
          end
        | Return(_, xs, lets, vr, a) ->
          List.iter2_exn xs vs
            ~f:(fun x v -> Ident.Table.set rho ~key:x ~data:v);
          trace_lets lets;
          let vr' = subst_value (Ident.Table.find_exn rho) vr in
          let lets = flush_lets () in
          Return(l0, x0, lets, vr', a)
      end in
  let v0 = List.map x0 ~f:(fun x -> Var x) in
  List.iter2_exn x0 v0
    ~f:(fun x v -> Ident.Table.set rho ~key:x ~data:v);
  trace_block i0 v0

let trace (func : Ssa.t) =
  let blocks = func.blocks in
  let traced = Ident.Table.create () in
  let res_blocks = Ident.Table.create () in
  let rec trace_blocks i =
    if not (Ident.Table.mem traced i) then
      begin
        Ident.Table.set traced ~key:i ~data:();

        let b = trace_block blocks i in
        Ident.Table.set res_blocks (label_of_block b).name b;
        List.iter (targets_of_block b) ~f:(fun l -> trace_blocks l.name)
      end in
  trace_blocks (func.entry_label.name);
  Ssa.make
    ~func_name: func.func_name
    ~entry_label: func.entry_label
    ~blocks: res_blocks
    ~return_type: func.return_type

(**
   Shortcutting jumps
*)
let shortcut_block blocks i0 =
  let block = Ident.Table.find_exn blocks i0 in
  let subst xs vs =
    let rho = List.zip_exn xs vs in
    fun y -> List.Assoc.find rho y
             |> Option.value ~default:(Var y) in

  let shortcut_value (i : label) v =
    let visited = Ident.Table.create () in
    let rec shortcut_value (i : label) v =
      if Ident.Table.mem visited i.name then
        i, v
      else
        begin
          Ident.Table.add_exn visited ~key:i.name ~data:();
          let block = Ident.Table.find_exn blocks i.name in
          match block with
          | Direct(_, x, [], vr, dst) ->
            let vr' = List.map vr ~f:(subst_value (subst x v)) in
            shortcut_value dst vr'
          | Branch(_, x, [], (_, _, vc, cases)) ->
            let vc' = subst_value (subst x v) vc in
            begin
              match vc' with
              | In((_, i, vi), _) ->
                let (y, vd, dst) = List.nth_exn cases i in
                let vd' = List.map vd
                            ~f:(fun w -> subst_value (fun z -> if y = z then vi else Var z)
                                           (subst_value (subst x v) w)) in
                shortcut_value dst vd'
              | _ ->
                i, v
            end
          | Unreachable _
          | Direct _
          | Branch _
          | Return _ ->
            i, v
        end in
    shortcut_value i v in

  match block with
  | Direct(l, x, lets, vr, dst) ->
    let dst', vr' = shortcut_value dst vr in
    Direct(l, x, lets, vr', dst')
  | Branch(l, x, lets, (id, params, vc, cases)) ->
    let cases' = List.map cases
                   ~f:(fun (y, vd, dst) ->
                     let dst', vd' = shortcut_value dst vd in
                     (y, vd', dst')) in
    Branch(l, x, lets, (id, params, vc, cases'))
  | Unreachable _
  | Return _ -> block

let shortcut_jumps (func : Ssa.t) =
  let blocks = func.blocks in
  let traced = Ident.Table.create () in
  let res_blocks = Ident.Table.create () in
  let rec shortcut_blocks i =
    if not (Ident.Table.mem traced i) then
      begin
        Ident.Table.set traced ~key:i ~data:();

        let b = shortcut_block blocks i in
        Ident.Table.set res_blocks (label_of_block b).name b;
        List.iter (targets_of_block b) ~f:(fun l -> shortcut_blocks l.name)
      end in
  shortcut_blocks (func.entry_label.name);
  Ssa.make
    ~func_name: func.func_name
    ~entry_label: func.entry_label
    ~blocks: res_blocks
    ~return_type: func.return_type
