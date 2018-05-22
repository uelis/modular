(** Representation of low-level types.

    This modules represents the first-order value types that
    are used in the low-level language.

    {v A,B ::= 'a | int | A1 * ... * An | box<A> | data<A1,...,A_n>  v}

    The type [box<A>] is intended to contain boxed values of type [A].

    Algebraic data types may be recursive, but each recursive occurrence
    must appear under a box.
*)

open Core_kernel

type 'a sgn =
  | IntB
  | BoxB of 'a
  | TupleB of 'a list
  | DataB of Ident.t * 'a list
  [@@deriving sexp]

include Uftype.S with type 'a Sgn.t = 'a sgn

(** Representation of algebraic data types.
*)
module Data:
sig
  (** Data type names, e.g. "list" *)
  type id = Ident.t

  (** Name of the n-ary sum type *)
  val sumid : int -> id

  (** Name of the bool type *)
  val boolid : id

  (** Number of type parameters of a data type.
      For example, pair<'a,'b> has two parameters *)
  val param_count : id -> int

  (** Number of constructors *)
  val constructor_count : id -> int

  (** Names of the constructors *)
  val constructor_names : id -> Ident.t list

  (** Given a name of a data type and a list of its type parameters,
      returns the types of the constructors of the type.
      The argument list must have the same length as the value
      returned by [params]. *)
  val constructor_types : id -> t list -> t list

  (** The data type is recursive. *)
  val is_recursive: id -> bool

  (** Non-discriminated unions are possible.*)
  val is_discriminated: id -> bool

  (** Look up a constructor by name. *)
  val find_constructor: Ident.t -> id * int

  (** Add a new data type, initially with no constructors. *)
  val make : id -> param_count:int -> discriminated:bool -> unit

  (** Add a constructor.
      The call [add_constructor id name params a] adds a
      constructor of type "[name: a -> id<params>]", where
      [id<params>] means the instantiation of the data type
      at the parameters [params].

      To add a constructor [cons: 'a -> list<'a>], one would
      call [add_constructor "list" "cons" ['a] 'a].

      Preconditions:
      - No constructor called [name] is already defined.
      - [params] is a list of type variables.
      - The free type variables in [a] are contained in [params].
  *)
  val add_constructor : id -> Ident.t -> t list -> t -> unit
end

val unitB : t
val intB : t
val pairB : t -> t -> t
val boolB : t
val sumB : t list -> t
