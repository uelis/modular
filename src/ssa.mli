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

(** SSA values and terms *)
type value =
  | Var of Ident.t
  | Unit
  | Tuple of value list
  | In of (Basetype.Data.id * int * value) * Basetype.t
  | Proj of value * int * Basetype.t list
  | Select of value * (Basetype.Data.id * Basetype.t list) * int
  | Undef of Basetype.t
  | IntConst of int
type term =
  | Val of value
  | Const of op_const * value

(** Substition of values in values *)
val subst_value: (Ident.t -> value) -> value -> value

(** Substition of values in terms *)
val subst_term: (Ident.t -> value) -> term -> term

(** Straight-line programs are given by let bindings *)
type let_binding =
  | Let of (Ident.t * Basetype.t) * term

(** A block is a list of let bindings in reverse order. *)
type let_bindings = let_binding list

(** Programs consist of a list of blocks, which each defines a label.*)
type label = {
  name: Ident.t;
  arg_types: Basetype.t list
}

(** Program blocks *)
type block =
    Unreachable of label
  | Direct of label * (Ident.t list) * let_bindings * (value list) * label
  | Branch of label * (Ident.t list) * let_bindings *
              (Basetype.Data.id * Basetype.t list * value *
               (Ident.t * (value list) * label) list)
  | Return of label * (Ident.t list) * let_bindings * value * Basetype.t

(** Return the label defined by a block *)
val label_of_block: block -> label

(** Return the jump targets of a block *)
val targets_of_block: block -> label list

(** A program in SSA form. *)
type t = private {
  func_name : string;
  entry_label: label;
  blocks : block list;
  return_type: Basetype.t;
}

(** Construct a SSA program from its part.
    This function verifies the representation invariants and
    verifies the program for type correctness, if assertions
    are enabled. *)
val make:
  func_name:string ->
  entry_label:label ->
  blocks: block list ->
  return_type: Basetype.t ->
  t

val fprint_value : Out_channel.t -> value -> unit
val fprint_term : Out_channel.t -> term -> unit
val fprint_letbndgs : Out_channel.t -> let_bindings -> unit
val fprint_block : Out_channel.t -> block -> unit
val fprint_func : Out_channel.t -> t -> unit
