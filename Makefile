all: native

native:
	corebuild modular.native

clean:
	rm -rf *.cmo *.cmx *.cmi parser.ml lexer.ml parser.mli _build *.byte *.native

veryclean:
	rm -f *.ssa *.ssa.traced *.ssa.shortcut *.ll *.bc
