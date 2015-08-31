# Translation of Call-by-Value PCF to Int

This is a very small experimental implementation of a typed closure
conversion from call-by-value PCF to Int.

The aim is to validate the correctness of the typed closure conversion
experimentally and to be able to consider example of how higher-order
PCF programs are translated to first-order code using the interactive
interpretation in Int. In particular, quantification over first-order
types is removed and the possible type instances are represented using
union types, which are inferred.

Currently, this implementation itself is quite slow and is intended
only for small experiments.

## Small Example

* Source: [fib.cbv](fib.cbv)
* Generated first-order program: [fib.ssa](fib.ssa)
* Generated LLVM code: [fib.ll](fib.ll)

## Building

This depends on (intc)[http://github.com/uelis/intc] being installed and available
in Ocamlfind. The Makefile there has a target `locallib`, so that
`make locallib` should be enough for the installation.
