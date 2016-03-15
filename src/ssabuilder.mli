(** Simple builder interface for constructing ssa blocks.*)

type value
val typeof: value -> Basetype.t

val blocks: Ssa.block Ident.Table.t
val reset: unit -> unit

val begin_block: ?may_append:bool -> Ssa.label -> value list
val begin_block1: ?may_append:bool -> Ssa.label -> value * value list
val begin_block2: ?may_append:bool -> Ssa.label -> value * value * value list
val begin_block3: ?may_append:bool -> Ssa.label -> value * value * value * value list
val begin_block4: ?may_append:bool -> Ssa.label -> value * value * value * value * value list

val unit: value
val intconst: int -> value
val boolconst: bool -> value
val primop: Ssa.op_const -> value -> value

val tuple: value list -> value
val untuple: value -> value list

val pair: value ->value -> value
val unpair: value -> value * value

val proj: value -> int -> value
val inj: int -> value -> Basetype.t -> value
val select: value -> int -> value

val box: value -> value
val unbox: value ->value

val project: value -> Basetype.t -> value
val embed: value -> Basetype.t -> value

val end_block_jump: Ssa.label -> value list -> unit
val end_block_unreachable: unit -> unit
val end_block_case: value -> ((value -> Ssa.label * (value list)) list) -> unit
val end_block_return: value -> unit
