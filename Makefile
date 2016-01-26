CFLAGS = -cflags "-g"  -cflags "-w A-4-33-40-41-42-43-34-44" -cflags -strict-sequence
OCAMLBUILD = ocamlbuild -j 0 -use-ocamlfind -tag thread -syntax camlp4o -pkg sexplib.syntax ${CFLAGS}

all: native

native:
	${OCAMLBUILD} modular.native

test:
	${OCAMLBUILD} test.native
	./test.native

clean:
	rm -rf *.cmo *.cmx *.cmi parser.ml lexer.ml parser.mli _build *.byte *.native

veryclean:
	rm -f *.ssa *.ssa.traced *.ssa.shortcut *.ll *.bc
