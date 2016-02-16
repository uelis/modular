#!/bin/sh

llvm-link $1.bc rt/stack.bc rt/gc.bc | opt -always-inline -O3 | llc -O3 | gcc -x assembler - -o $1

