{ lib, vscode-utils, unzip }:

vscode-utils.buildVscodeExtension
{
  name = "axi-syntax";
  version = "0.1.0";
  #src = ./.;
  src = ./axi-syntax-0.1.0.vsix;
  sourceRoot = ".";
  #vsix = ./axi-syntax-0.1.0.vsix;

  # Explicitly unpack the .vsix file:
  unpackPhase = ''
    ${unzip}/bin/unzip $src
    sourceRoot=extension
  '';

  vscodeExtPublisher = "khalani";
  vscodeExtName = "axi-syntax";
  vscodeExtUniqueId = "khalani.axi-syntax";

  meta = with lib;
  {
    description = "Axi syntax highlighting";
    license = licenses.mit;
    platforms = platforms.all;
  };
}
