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

    shellHook = mkShellHook "Formalization"
    ''
      echo -e "''${GREEN}./build.sh''${RESET}   — Regenerate the makefile, then build"
      echo -e "''${GREEN}make''${RESET}         — Build"
      echo -e "''${GREEN}make clean''${RESET}   — Clean build artifacts"
      echo -e "''${GREEN}coqide''${RESET}       — Start CoqIDE"
    '';
  };

  theory = pkgs.mkShell
  {
    inputsFrom = [ derivations.theory ];

    shellHook = mkShellHook "Theory"
    ''
      echo -e "''${GREEN}./build.sh''${RESET}   — Build PDF"
      echo -e "''${GREEN}latexmk''${RESET}      — Build PDF manually"
      echo -e "''${GREEN}latexmk -C''${RESET}   — Clean build artifacts"
    '';
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

    shellHook = mkShellHook "Prototype"
    ''
      echo -e "''${GREEN}cabal build''${RESET}  — Build"
      echo -e "''${GREEN}cabal repl''${RESET}   — Start GHCi"
      echo -e "''${GREEN}cabal test''${RESET}   — Run tests"
      echo -e "''${GREEN}cabal clean''${RESET}  — Clean build artifacts"
    '';
  };

  vscode-extension = pkgs.mkShell
  {
    inputsFrom = [ derivations.vscode-extension ];
    shellHook = mkShellHook "VSCode extension"
    ''
      EXT_LINK=$HOME/.vscode/extensions/pevnik-labs.axi-syntax-highlighting
      EXT_TARGET=${derivations.vscode-extension}/share/vscode/extensions/pevnik-labs.axi-syntax-highlighting

      if [ -d /etc/nixos ]; then
        echo "NixOS detected. Add to configuration.nix:"
        echo ""
        echo "  programs.vscode.extensions ="
        echo "  ["
        echo "    (pkgs.callPackage path-to-Axi/default.nix {}).vscode-extension)"
        echo "  ];"
      else
        mkdir -p $HOME/.vscode/extensions
        ln -sfn $EXT_TARGET $EXT_LINK
        echo "VSCode extension installed."
      fi
    '';
  };

  tree-sitter-grammar = pkgs.mkShell
  {
    inputsFrom = [ derivations.tree-sitter-grammar ];

    shellHook = mkShellHook "tree-sitter parser"
    ''
      echo -e "''${GREEN}./tree-sitter-axi/build.sh''${RESET} — Build and test"
      echo -e "''${GREEN}tree-sitter init --update''${RESET}  — Regenerate bindings"
      echo -e "''${GREEN}tree-sitter generate''${RESET}       — Regenerate parser from grammar.js"
      echo -e "''${GREEN}tree-sitter build''${RESET}          — Build .c"
      echo -e "''${GREEN}tree-sitter build --wasm''${RESET}   — Build .wasm"
      echo -e "''${GREEN}tree-sitter test''${RESET}           — Run tests"
      echo -e "''${GREEN}tree-sitter parse''${RESET}          — Parse a file"
    '';
  };

  # The default shell has everything.
  default = pkgs.mkShell
  {
    inputsFrom = [ formalization theory prototype vscode-extension tree-sitter-grammar ];

    shellHook = mkShellHook "all"
    ''
      echo -e "''${GREEN}nix build .#formalization''${RESET}      — Build Coq formalization"
      echo -e "''${GREEN}nix build .#theory''${RESET}             — Build theory PDF"
      echo -e "''${GREEN}nix build .#prototype''${RESET}          — Build Haskell prototype"
      echo -e "''${GREEN}nix build .#vscode-extension''${RESET}   — Build VSCode extension"
      echo -e "''${GREEN}nix build .#tree-sitter-grammar''${RESET} — Build tree-sitter parser"
      echo -e "''${GREEN}nix build''${RESET}                      — Build everything"
      echo ""
      echo -e "''${GREEN}nix develop .#formalization''${RESET}    — Coq shell (has CoqIDE)"
      echo -e "''${GREEN}nix develop .#theory''${RESET}           — Theory TeX shell"
      echo -e "''${GREEN}nix develop .#prototype''${RESET}        — Haskell shell"
      echo -e "''${GREEN}nix develop .#vscode-extension''${RESET} — VSCode extension shell"
      echo -e "''${GREEN}nix develop .#tree-sitter-grammar''${RESET} — tree-sitter shell"
    '';
  };

in
{
  inherit formalization theory prototype vscode-extension tree-sitter-grammar default;
}
