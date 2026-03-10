{ pkgs ? import <nixpkgs> {} }:

pkgs.stdenv.mkDerivation
{
  pname = "tree-sitter-axi";
  version = "0.1.0";

  meta = with pkgs.lib;
  {
    description = "A tree-sitter grammar for Axi.";
    license = licenses.asl20;
    platforms = platforms.linux;
  };

  enableParallelBuilding = true;

  src = pkgs.lib.cleanSource ./.;

  nativeBuildInputs = with pkgs;
  [
    tree-sitter
    emscripten
    nodejs
  ];

  buildPhase =
  ''
    export HOME=$(mktemp -d)
    tree-sitter generate
    tree-sitter build --output axi.so
    tree-sitter build --wasm --output tree-sitter-axi.wasm
  '';

  doCheck = true;
  checkPhase =
  ''
    tree-sitter test
  '';

  installPhase =
  ''
    mkdir -p $out/lib
    mkdir -p $out/share/tree-sitter-axi

    cp axi.so $out/lib/libtree-sitter-axi.so
    cp tree-sitter-axi.wasm $out/share/tree-sitter-axi/
    cp -r src $out/share/tree-sitter-axi/
  '';
}
