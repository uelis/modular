# modular
Implementation of modular translation for call-by-value PCF

(Some documentation will be added in the next few days.)

## Compilation

The translation is writen in OCaml and uses LLVM for code generation.
It depends on Jane Street's Core_kernel library and the OCaml LLVM bindings.

On Ubuntu, LLVM can be installed using `apt-get install llvm`.
The OCaml libraries are most easily installed using the
OCaml Package Manager (OPAM), which can be obtained from (http://opam.ocamlpro.com).
On Ubuntu, OPAM can be installed with `apt-get install opam`.

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

