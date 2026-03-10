{ pkgs ? import <nixpkgs> {} }:

let
  # We add CoqIDE to Coq and provide `coqide as an alias for `rocqide`.
  coq-with-ide = pkgs.coq_9_1.override { buildIde = true; };
  coqide-alias = pkgs.writeShellScriptBin "coqide"
  ''
    exec ${coq-with-ide}/bin/rocqide "$@"
  '';
in

pkgs.mkShell
{
  # We can't reuse build inputs from `default.nix` because they don't have CoqIDE.
  buildInputs = with pkgs;
  [
    coq-with-ide
    coqide-alias
    rocqPackages_9_1.stdlib
  ];

  shellHook =
  ''
    GREEN="\033[1;32m"
    RESET="\033[0m"

    export PROJECT_ROOT=$(pwd)
    export PS1="\n\[''${GREEN}\]Axi\''${PWD#\''$PROJECT_ROOT}>\[''${RESET}\] "

    echo ""
    echo "Axi formalization development shell"
    echo ""
    echo -e "''${GREEN}./build.sh''${RESET}   — Regenerate the makefile, then build"
    echo -e "''${GREEN}make''${RESET}         — Build"
    echo -e "''${GREEN}make clean''${RESET}   — Clean build artifacts"
    echo -e "''${GREEN}coqide''${RESET}       — Start CoqIDE"
  '';
}
