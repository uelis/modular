(** Progams in functional SSA form *)
open Core_kernel.Std

type value_const =
  | Cundef of Basetype.t
  | Cintconst of int

type op_const =
  | Cprint of string
  | Cintadd
  | Cintsub
  | Cintmul
  | Cintdiv
  | Cinteq
  | Cintlt
  | Cintslt
  | Cintshl
  | Cintshr
  | Cintsar
  | Cintand
  | Cintor
  | Cintxor
  | Cintprint
  | Cgcalloc of Basetype.t
  | Calloc of Basetype.t
  | Cfree of Basetype.t
  | Cload of Basetype.t
  | Cstore of Basetype.t
  | Cpush of Basetype.t
  | Cpop of Basetype.t
  | Ccall of string * Basetype.t * Basetype.t

type constructor = int * (Basetype.Data.id * Basetype.t list)

(** SSA values and terms *)
type value =
  | IntConst of int
  | Var of Ident.t
  | Tuple of value list
  | Proj of value * int * Basetype.t list
  | In of constructor * value
  | Select of constructor * value
  | Undef of Basetype.t

type term =
  | Const of op_const * value

(** Substition of values in values *)
val subst_value: (Ident.t -> value) -> value -> value

(** Substition of values in terms *)
val subst_term: (Ident.t -> value) -> term -> term

(** Straight-line programs are given by let bindings *)
type let_binding =
  | Let of Ident.t * term

(** A block is a list of let bindings in reverse order. *)
type let_bindings = let_binding list

(** Programs consist of a list of blocks, which each defines a label.*)
type label = {
  name: Ident.t;
  arg_types: Basetype.t list;
  debug_loc: Ast.Location.t
}

type transfer =
  | Unreachable
  | Direct of label * (value list)
  | Branch of value * (Basetype.Data.id * Basetype.t list) * (Ident.t * label * (value list)) list
  | Return of value * Basetype.t

(** Program blocks *)
type block =
  { label : label;
    args : Ident.t list;
    body : let_bindings;
    jump : transfer }

(** Return the jump targets of a block *)
val targets_of_block: block -> label list

(** A program in SSA form. *)
type t = private {
  func_name : string;
  entry_label: label;
  blocks : block Ident.Table.t;
  return_type: Basetype.t;
}

(** Iterates over all blocks beginning with the entry label such that any block
    may appear only if it is the target of a jump from a block that has
    appeared before. *)
val iter_reachable_blocks: f:(block -> unit) -> t -> unit

(** Construct a SSA program from its part.
    This function verifies the program for type correctness,
    if assertions are enabled. *)
val make:
  func_name:string ->
  entry_label:label ->
  blocks: block Ident.Table.t ->
  return_type: Basetype.t ->
  t

val fprint_value : Out_channel.t -> value -> unit
val fprint_term : Out_channel.t -> term -> unit
val fprint_letbndgs : Out_channel.t -> let_bindings -> unit
val fprint_block : Out_channel.t -> block -> unit
val fprint_func : Out_channel.t -> t -> unit
