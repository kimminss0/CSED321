#!/bin/sh

eval $(opam env --switch=4.14.2 --set-switch)
make clean
cp typing_stub.ml typing.ml
make
echo "LSP setup: compiled with ocamlc $(ocamlc --version)"