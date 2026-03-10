{ pkgs ? import <nixpkgs> {} }:

pkgs.vscode-utils.buildVscodeExtension
{
  pname = "axi-syntax-highlighting";
  version = "0.1.0";

  vscodeExtPublisher = "pevnik-labs";
  vscodeExtName      = "axi-syntax-highlighting";
  vscodeExtUniqueId  = "pevnik-labs.axi-syntax-highlighting";

  meta = with pkgs.lib;
  {
    description = "Axi syntax highlighting for VSCode";
    license = licenses.asl20;
    platforms = platforms.linux;
  };

  enableParallelBuilding = true;

  src = ./.;

  unpackPhase =
  ''
    cp -r $src extension
    chmod -R u+w extension
    sourceRoot=extension
  '';
}
