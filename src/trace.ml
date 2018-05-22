open Core_kernel
open Ssa

let fresh_var _ = Ident.fresh "z"

(**
   Tracing
*)
let trace_block blocks i0 =
  let block = Ident.Table.find_exn blocks i0 in
  let l0 = block.label in
  let x0 = List.map ~f:fresh_var l0.arg_types in

  (* substitution *)
  let rho = Ident.Table.create () in
  (* current body *)
  let lets = ref [] in
  (* already visited labels *)
  let visited = Ident.Table.create () in

  let trace_let = function
    | Let(x, t) ->
      let t' = subst_term (Ident.Table.find_exn rho) t in
      let x' = fresh_var () in
      Ident.Table.set rho ~key:x ~data:(Var x');
      lets := Let(x', t') :: !lets in
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
      let dst = block.label in
      { label = l0;
        args = x0;
        body = lets;
        jump = Direct(dst, vs) }
    | _ ->
      begin
        Ident.Table.change visited i (function None -> Some 1
                                             | Some i -> Some (i+1));
        let block_body xs lets =
          List.iter2_exn xs vs
            ~f:(fun x v -> Ident.Table.set rho ~key:x ~data:v);
          trace_lets lets in
        match block.jump with
        | Unreachable ->
          { label = l0;
            args = x0;
            body = [];
            jump = Unreachable }
        | Direct(dst, vr) ->
          block_body block.args block.body;
          let vr' = List.map vr ~f:(subst_value (Ident.Table.find_exn rho)) in
          trace_block dst.name vr'
        | Branch(vc, (id, params), cases) ->
          block_body block.args block.body;
          let vc' = subst_value (Ident.Table.find_exn rho) vc in
          begin
            match vc' with
            | Inj((i, _), vi) ->
              let (y, dst, vd) = List.nth_exn cases i in
              Ident.Table.set rho ~key:y ~data:vi;
              let vd' = List.map vd ~f:(subst_value (Ident.Table.find_exn rho)) in
              trace_block dst.name vd'
            | _ ->
              let lets = flush_lets () in
              let cases' =
                List.map cases
                  ~f:(fun (y, dst, vd) ->
                    let y' = fresh_var () in
                    Ident.Table.set rho ~key:y ~data:(Var y');
                    let vd' = List.map vd ~f:(subst_value (Ident.Table.find_exn rho)) in
                    (y', dst, vd')) in
              { label = l0;
                args = x0;
                body = lets;
                jump = Branch(vc', (id, params), cases') }
          end
        | Return(vr, a) ->
          block_body block.args block.body;
          let vr' = subst_value (Ident.Table.find_exn rho) vr in
          let lets = flush_lets () in
          { label = l0;
            args = x0;
            body = lets;
            jump = Return(vr', a) }
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
        Ident.Table.set res_blocks b.label.name b;
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
    fun y -> List.Assoc.find ~equal:(=) rho y
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
          match block.body, block.jump with
          | [], Direct(dst, vr) ->
            let vr' = List.map vr ~f:(subst_value (subst block.args v)) in
            shortcut_value dst vr'
          | [], Branch(vc, _, cases) ->
            let vc' = subst_value (subst block.args v) vc in
            begin
              match vc' with
              | Inj((i, _), vi) ->
                let (y, dst, vd) = List.nth_exn cases i in
                let vd' = List.map vd ~f:(fun w ->
                  subst_value
                    (fun z -> if y = z then vi else Var z)
                    (subst_value (subst block.args v) w)) in
                shortcut_value dst vd'
              | _ ->
                i, v
            end
          | _, Unreachable
          | _, Direct _
          | _, Branch _
          | _, Return _ ->
            i, v
        end in
    shortcut_value i v in

  match block.jump with
  | Direct(dst, vr) ->
    let dst', vr' = shortcut_value dst vr in
    { block with jump = Direct(dst', vr') }
  | Branch(vc, (id, params), cases) ->
    let cases' = List.map cases ~f:(fun (y, dst, vd) ->
      let dst', vd' = shortcut_value dst vd in
      (y, dst', vd')) in
    { block with jump = Branch(vc, (id, params), cases') }
  | Unreachable
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
        Ident.Table.set res_blocks b.label.name b;
        List.iter (targets_of_block b) ~f:(fun l -> shortcut_blocks l.name)
      end in
  shortcut_blocks (func.entry_label.name);
  Ssa.make
    ~func_name: func.func_name
    ~entry_label: func.entry_label
    ~blocks: res_blocks
    ~return_type: func.return_type
