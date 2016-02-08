# Modular
(More documentation will be added in the next few days.)

This program implements the modular translation of call-by-value PCF that is
described in detail in
[this draft paper](http://www2.tcs.ifi.lmu.de/~schoepp/Docs/modular.pdf). The
program takes as input a PCF program and performs the following steps:

  1. Infer simple types for the input program.
  2. Infer type annotations to obtain a legal derivation in the
     annotated PCF type system, which is described in the paper.
  3. Translate the annotated typing derivation to a low-level program.
  4. Generate LLVM-bitcode from the low-level program.

The low-level language used in the implementation is a variant of that
described in the paper. The main difference is that it uses a more low-level
representation of recursive types. The low-level language does not support
recursive types as such, but instead supports a type `box<A>` of typed pointers
to the heap. Recursive types can be implemented using pointers to the heap. For
example, lists are available as

```
  type list<'a> =
        Nil of unit
        | Cons of 'a * box<list<'a>>
```

The translation in steps 2 and 3 is implemented as it is described in the
paper. As described there, in step 2 there are many different ways of solving
the constraints on type annotations. The implementation currently uses the
simple solution using recursive types described in the paper. For example, the
two constraints `C <= 'a` and `'b *'a <= 'a` would be solved by letting `'a` be
the following type:

```
  type cons<'b> = Cons1 of C
                | Cons2 of 'b * box<cons<'b>>
```

This solution amounts to a type of lists. The appearance of `box` means that
these lists are stored as linked lists, where the tail is always a pointer to
the heap. This use of the heap is somewhat inefficient and one may want to
replace it by stack-allocated data, as described in the paper. This was done
experimentally in an
[earlier version of the translation](https://github.com/uelis/cbv2int), which
shows that such a change is not hard to do and significantly improves
performance. Here the simple solution is implemented first, as it works without
having to assume a stack and may have applications, e.g. for hardware
synthesis.


## Installation

The translation is written in OCaml and uses LLVM for code generation. It
depends on Jane Street's Core_kernel library and the OCaml LLVM bindings.

On Ubuntu, LLVM can be installed using `apt-get install llvm`. The OCaml
libraries are most easily installed using the OCaml Package Manager (OPAM),
which can be obtained from (http://opam.ocamlpro.com). On Ubuntu, OPAM can be
installed with `apt-get install opam`.

```
  opam install core_kernel
  opam install llvm
```

It may be necessary to pin the LLVM binding to the version of LLVM that is
installed on the system. For example, pinning the LLVM binding to version 3.6
may be done as follows:

```
  opam pin add llvm 3.6
```

Having installed these dependencies, the translation may be compiled and invoked as:

```
  make
  ./modular.native test17fib.cbv
```

## Source Language

The input language is currently a simple version of PCF. Input files are
expected to have the form

```
  let x1 = t1
  let x2 = t2
  ...
  let xn = tn
```

Terms can be formed using the following concrete syntax:

```
  s,t  ::=  x  |  let x = s in t  |  \x -> t  |  s t  |  fix f x -> t
         |  if s = t then t1 else t2
         |  0  |  -1  |  1  |  -2  |  2  | ...
         |  s + t  |  s - t  |  s * t  |  s / t  |  print(t)
```

The concrete syntax for types is

```
  X, Y  ::=  Nat | X -> Y
```

The term `print(t)` prints the value of the term `t`, which must have type `Nat`.
The value of `print(t)` is that of `t`.

For example, the following program prints the 20-th Fibonacci number

```
  let fib =
    fix fib x -> let x1 = x - 1 in
                 let x2 = x - 2 in
                 if x1 = 0 then 1 else
                 if x2 = 0 then 1 else
                 (fib x1) +  (fib x2)
  let main =
    print (fib 20)
```

## Usage

The implementation produces an LLVM-bitcode file for each toplevel definition
in the input file. If the file `fib.cbv` has the content of the Fibonacci
example above, then the call

```
  > ./modular.native fib.cbv
```

prints the types of `fib` and `main` (namely `Nat -> Nat` and `Nat`
respectively) and produces LLVM bitcode files `fib.bc` and `main.bc` for
them. While both have a well-specified interface, as explained in the paper,
without further linking one can currently run only programs of base type. It is
possible to link `fib.bc` to an assembly module implementing the function
argument, but one needs to do the linking by hand, currently.

To generate an executable from `main.bc` using the LLVM compiler tools, one may
invoke the script `llvm_compile.sh` as follows:

```
  > ./llvm_compile main
```

This should generate an executable `main` that prints the 20-th Fibonacci number.

```
  > ./main
  6765
```

### Printing Type Annotations

By default, the implementation just shows simple types. Type annotations can be
shown using the command-line argument `--type-details`. The concrete syntax for
annotated types is as follows:

```
  X, Y  ::=  Nat[A] | X -{A, C}-> Y
```

For example,

```
  > ./modular.native --type-details fib.cbv
```

gives the following types

```
  fib : ['g](Nat[unit * 'f + 'e] -{box<(conty0<unit>)>, unit}-> Nat['d])
  main : Nat['k]
```
  
where
  
```
  type conty0<'a> = conty0_0 of box<(conty0<'a>)> * (unit * int * 'a)
                  | conty0_1 of box<(conty0<'a>)> * int
```
