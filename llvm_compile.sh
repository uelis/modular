#!/bin/sh

llvm-link $1.bc stack.ll gc.ll | opt -always-inline -O3 | llc -O3 | gcc -x assembler - -o $1

