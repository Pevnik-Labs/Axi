{ pkgs ? import <nixpkgs> {}, compiler ? "ghc984" }:

let
  haskellPackages = pkgs.haskell.packages.${compiler};
in

haskellPackages.shellFor
{
  packages = _:
  [
    (import ./default.nix { inherit pkgs; })
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
}
