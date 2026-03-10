{ pkgs ? import <nixpkgs> {} }:

let
  vscode-extension = import ./default.nix { inherit pkgs; };
in

pkgs.mkShell
{
  inputsFrom = [ vscode-extension ];

  shellHook =
  ''
    GREEN="\033[1;32m"
    RESET="\033[0m"

    export PROJECT_ROOT=$(pwd)
    export PS1="\n\[''${GREEN}\]Axi\''${PWD#\''$PROJECT_ROOT}>\[''${RESET}\] "

    echo ""
    echo "Axi VSCode extension development shell"
    echo ""

    EXT_LINK=$HOME/.vscode/extensions/pevnik-labs.axi-syntax-highlighting
    EXT_TARGET=${vscode-extension}/share/vscode/extensions/pevnik-labs.axi-syntax-highlighting

    if [ -d /etc/nixos ]; then
      echo "NixOS detected. Add to configuration.nix:"
      echo ""
      echo "  programs.vscode.extensions ="
      echo "  ["
      echo "    (pkgs.callPackage path-to-Axi-repo/default.nix {}).vscode-extension)"
      echo "  ];"
    else
      mkdir -p $HOME/.vscode/extensions
      ln -sfn $EXT_TARGET $EXT_LINK
      echo "VSCode extension installed."
    fi
  '';
}
