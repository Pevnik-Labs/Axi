{ pkgs ? import <nixpkgs> {} }:

let
  theory              = import ./Theory/shell.nix          { inherit pkgs; };
  formalization       = import ./Formalization/shell.nix   { inherit pkgs; };
  prototype           = import ./axii/shell.nix            { inherit pkgs; };
  vscode-extension    = import ./vscode-axi/shell.nix      { inherit pkgs; };
  tree-sitter-grammar = import ./tree-sitter-axi/shell.nix { inherit pkgs; };
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
