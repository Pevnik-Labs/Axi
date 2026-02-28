{ pkgs ? import <nixpkgs> {} }:

let
  # Derivations imported from default.nix
  derivations = import ./default.nix { inherit pkgs; };

  # A custom shell hook that display some useful info.
  # `name` is the name of the shell (formalization, slides, theory, prototype).
  # `extra` is additional info to be printed when entering the shell.
  mkShellHook = name: extra:
  ''
    GREEN="\033[1;32m"
    RESET="\033[0m"

    export PROJECT_ROOT=$(pwd)
    export PS1="\n\[''${GREEN}\]Axi\''${PWD#\''$PROJECT_ROOT}>\[''${RESET}\] "

    echo ""
    echo -e "Axi development shell for ${name}"
    echo ""
    ${extra}
  '';

  formalizationHook = mkShellHook "Formalization"
  ''
    echo -e "''${GREEN}./build.sh''${RESET}   — Regenerate the makefile, then build"
    echo -e "''${GREEN}make''${RESET}         — Build"
    echo -e "''${GREEN}make clean''${RESET}   — Clean build artifacts"
    echo -e "''${GREEN}coqide''${RESET}       — Start CoqIDE"
  '';

  texHook = name: mkShellHook name
  ''
    echo -e "''${GREEN}./build.sh''${RESET}   — Build PDF"
    echo -e "''${GREEN}latexmk''${RESET}      — Build PDF manually"
    echo -e "''${GREEN}latexmk -C''${RESET}   — Clean build artifacts"
  '';

  prototypeHook = mkShellHook "Prototype"
  ''
    echo -e "''${GREEN}cabal build''${RESET}  — Build"
    echo -e "''${GREEN}cabal repl''${RESET}   — Start GHCi"
    echo -e "''${GREEN}cabal test''${RESET}   — Run tests"
    echo -e "''${GREEN}cabal clean''${RESET}  — Clean build artifacts"
  '';

  allHook = mkShellHook "all"
  ''
    echo -e "''${GREEN}nix build .#formalization''${RESET}  — Build Coq formalization"
    echo -e "''${GREEN}nix build .#slides''${RESET}         — Build slides PDF"
    echo -e "''${GREEN}nix build .#theory''${RESET}         — Build theory PDF"
    echo -e "''${GREEN}nix build .#prototype''${RESET}      — Build Haskell prototype"
    echo -e "''${GREEN}nix build''${RESET}                  — Build everything"
    echo ""
    echo -e "''${GREEN}nix develop .#formalization''${RESET}  — Coq shell"
    echo -e "''${GREEN}nix develop .#slides''${RESET}         — Slides TeX shell"
    echo -e "''${GREEN}nix develop .#theory''${RESET}         — Theory TeX shell"
    echo -e "''${GREEN}nix develop .#prototype''${RESET}      — Haskell shell"
  '';

  # Individual shells.

  formalization = pkgs.mkShell
  {
    # We can't reuse build inputs from default.nix because we need to
    # add CoqIDE to Coq. We also want to provide `coqide` as an alias
    # for `rocqide`.
    buildInputs =
    let
      coq-with-ide = pkgs.coq_9_1.override { buildIde = true; };
      coqide-alias = pkgs.writeShellScriptBin "coqide"
      ''
        exec ${coq-with-ide}/bin/rocqide "$@"
      '';
    in with pkgs;
    [
      coq-with-ide
      coqide-alias
      rocqPackages_9_1.stdlib
    ];

    shellHook = formalizationHook;
  };

  theory = pkgs.mkShell
  {
    inputsFrom = [ derivations.theory ];
    shellHook = texHook "Theory";
  };

  slides = pkgs.mkShell
  {
    inputsFrom = [ derivations.slides ];
    shellHook = texHook "Slides";
  };

  haskellPackages = pkgs.haskell.packages.ghc984;
  prototype = haskellPackages.shellFor
  {
    nativeBuildInputs = with haskellPackages;
    [
      alex
      BNFC
      cabal-install
      happy
      #haskell-language-server
      hpack
    ];

    packages = _: [ derivations.prototype ];

    shellHook = prototypeHook;
  };

  # The default shell has everything.
  default = pkgs.mkShell
  {
    inputsFrom = [ formalization theory slides prototype ];
    shellHook = allHook;
  };

in
{
  inherit formalization theory slides prototype default;
}
