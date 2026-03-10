{ pkgs ? import <nixpkgs> {} }:

let
  theory              = import ./Theory/default.nix          { inherit pkgs; };
  formalization       = import ./Formalization/default.nix   { inherit pkgs; };
  prototype           = import ./axii/default.nix            { nixpkgs = pkgs; };
  vscode-extension    = import ./vscode-axi/default.nix      { inherit pkgs; };
  tree-sitter-grammar = import ./tree-sitter-axi/default.nix { inherit pkgs; };
in
{
  inherit theory formalization prototype vscode-extension tree-sitter-grammar;

  default = pkgs.symlinkJoin
  {
    name = "Axi";

    paths =
    [
      prototype
      theory
      formalization
      vscode-extension
      tree-sitter-grammar
    ];
  };
}
