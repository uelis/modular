# Modular
(More documentation will be added in the next few days.)

This program implements the modular translation of call-by-value PCF
that is described in detail in
[this draft paper](http://www2.tcs.ifi.lmu.de/~schoepp/Docs/modular.pdf).
The program takes as input a PCF program and performs the following steps:

  1. Infer simple types for the input program.
  2. Infer type annotations to obtain a legal derivation in the
     annotated PCF type system, which is described in the paper.
  3. Translate the annotated typing derivation to a low-level program.
  4. Generate LLVM-bitcode from the low-level program.

The low-level language used in the implementation is a variant of that described in the paper. The main difference is that it uses a more low-level
representation of recursive types. The low-level language does not support recursive types as such, but instead supports a type `box<A>` of typed
pointers to the heap. Recursive types can be implemented using pointers to the heap. For examples, lists are available as
```
  type list<'a> =
        Nil of unit
        | Cons of 'a * box<list<'a>>
```

The translation in steps 2 and 3 is implemented, as it is described in the paper. As described there, in step 2 there are many different ways of choosing
the solution to type annotations. The implementation currently uses the simple solution using recursive types described in the paper. For example, the two
constraints `C <= 'a` and `'b *'a <= 'a` would be solved by letting `'a` be the following type:
```
  type cons<'b> =
         Cons1 of C
        | Cons2 of 'b * box<cons<'b>>
```
This solution amounts to a type of lists. The appearance of `box` means that these lists are stored as linked lists, where the tail is always a pointer to
the heap. This use of the heap is somewhat inefficient and one may want to replace it by stack-allocated data, as described in the paper. This was done
experimentally in an [earlier version of the translation](https://github.com/uelis/cbv2int), which shows that such a change is not hard to do and significantly improves
performance. Here the simple solution is implemented first, as it works without having to assume a stack and may have applications, e.g. for hardware synthesis.


## Compilation

The translation is writen in OCaml and uses LLVM for code generation. It depends on Jane Street's Core_kernel library and the OCaml LLVM bindings.

On Ubuntu, LLVM can be installed using `apt-get install llvm`. The OCaml
libraries are most easily installed using the OCaml Package Manager (OPAM),
which can be obtained from (http://opam.ocamlpro.com). On Ubuntu, OPAM can be installed with `apt-get install opam`.

```
  opam install core_kernel
  opam install llvm
```

It may be necessary to pin the LLVM binding to the version of LLVM that is
installed on the system. For example, pinning the LLVM binding to version 3.6 may be done as follows:

```
  opam pin add llvm 3.6
```

Having installed these dependencies, the translation may be compiled and invoked as:

```
  make
  ./modular.native test17fib.cbv
```

