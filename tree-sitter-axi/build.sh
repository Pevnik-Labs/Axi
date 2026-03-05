#!/bin/sh
tree-sitter generate
tree-sitter build
tree-sitter build --wasm
tree-sitter test

