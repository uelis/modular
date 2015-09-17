CFLAGS = -cflags "-g"
OCAMLBUILD = ocamlbuild -j 0 -use-ocamlfind -tag thread -syntax camlp4o -pkg sexplib.syntax ${CFLAGS}

all: native

native:
	${OCAMLBUILD} cbv2int.native

byte:
	${OCAMLBUILD} cbv2int.byte

test:
	corebuild -j 0 test.native
	corebuild -j 0 test_inline.native
	./test.native
	./test_inline.native inline-test-runner intc -show-counts

clean:
	rm -rf *.cmo *.cmx *.cmi parser.ml lexer.ml parser.mli _build *.byte *.native

veryclean:
	rm -f *.ssa *.ssa.traced *.ssa.shortcut *.ll *.bc
