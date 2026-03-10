{ pkgs ? import <nixpkgs> {} }:

let
  tree-sitter-grammar = import ./default.nix { inherit pkgs; };
in

pkgs.mkShell
{
  inputsFrom = [ tree-sitter-grammar ];

  shellHook =
  ''
    GREEN="\033[1;32m"
    RESET="\033[0m"

    export PROJECT_ROOT=$(pwd)
    export PS1="\n\[''${GREEN}\]Axi\''${PWD#\''$PROJECT_ROOT}>\[''${RESET}\] "

    echo ""
    echo "Axi tree-sitter grammar development shell"
    echo ""
    echo -e "''${GREEN}./build.sh''${RESET}                 — Build and test"
    echo -e "''${GREEN}tree-sitter init --update''${RESET}  — Regenerate bindings"
    echo -e "''${GREEN}tree-sitter generate''${RESET}       — Regenerate parser from grammar.js"
    echo -e "''${GREEN}tree-sitter build''${RESET}          — Build .c"
    echo -e "''${GREEN}tree-sitter build --wasm''${RESET}   — Build .wasm"
    echo -e "''${GREEN}tree-sitter test''${RESET}           — Run tests"
    echo -e "''${GREEN}tree-sitter parse''${RESET}          — Parse a file"
  '';
}
