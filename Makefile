default: main

main: main.native

%.native: 
    ocamlbuild -use-ocamlfind $@
    mv $@ $*

.PHONY: test default