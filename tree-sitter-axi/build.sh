#!/bin/sh
tree-sitter generate
tree-sitter build --output axi.so
tree-sitter build --wasm --output tree-sitter-axi.wasm
tree-sitter test
