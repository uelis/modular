#!/bin/sh

llvm-link $1.bc | opt -always-inline -O3 | llc -O3 | gcc -x assembler - -x c gc.c -o $1

