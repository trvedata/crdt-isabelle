# Dependencies:
# Core Async

.SUFFIXES: .ml .byte .js .native

all: network.native wrapper.js

clean:
	rm -f *.{byte,js,native,cmo,cmi}

test: clean wrapper.js
	node -e 'const { counter } = require("./wrapper.js")'

.ml.native:
	corebuild -pkg async $@

.ml.byte:
	ocamlbuild -use-ocamlfind -lflag -g -pkgs js_of_ocaml,js_of_ocaml.ppx $@

.byte.js:
	js_of_ocaml --pretty -o $@ $<
