{ pkgs ? import <nixpkgs> {} }:

let
  theory              = import ./Theory/shell.nix          { inherit pkgs; };
  formalization       = import ./Formalization/shell.nix   { inherit pkgs; };
  vscode-extension    = import ./vscode-axi/shell.nix      { inherit pkgs; };
  tree-sitter-grammar = import ./tree-sitter-axi/shell.nix { inherit pkgs; };

  haskellPackages = pkgs.haskell.packages.ghc984;
  prototype = haskellPackages.shellFor
  {
    packages = _:
    [
      (import ./axii/default.nix { nixpkgs = pkgs; })
    ];

    nativeBuildInputs =
    [
      haskellPackages.alex
      haskellPackages.BNFC
      haskellPackages.cabal-install
      haskellPackages.happy
      haskellPackages.hpack

      # Use top-level HLS. The one from `haskellPackages` (v 9.8.4) is broken in nixpkgs.
      pkgs.haskell-language-server
    ];

    shellHook =
    ''
      GREEN="\033[1;32m"
      RESET="\033[0m"

      export PROJECT_ROOT=$(pwd)
      export PS1="\n\[''${GREEN}\]Axi\''${PWD#\''$PROJECT_ROOT}>\[''${RESET}\] "

      echo ""
      echo "Axi development shell for the Haskell prototype"
      echo ""
      echo -e "''${GREEN}cabal build''${RESET} — Build"
      echo -e "''${GREEN}cabal repl''${RESET}  — Start GHCi"
      echo -e "''${GREEN}cabal test''${RESET}  — Run tests"
      echo -e "''${GREEN}cabal clean''${RESET} — Clean build artifacts"
    '';
  };
in
{
  inherit theory formalization prototype vscode-extension tree-sitter-grammar;

  default = pkgs.mkShell
  {
    inputsFrom =
    [
      vscode-extension
      tree-sitter-grammar
      prototype
      formalization
      theory
    ];
  };
}
