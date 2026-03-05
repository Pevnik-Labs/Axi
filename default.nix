{ pkgs ? import <nixpkgs> {} }:

let
  # The Haskell prototype's build is managed by Cabal.
  haskellCompiler = "ghc984";
  prototype = pkgs.haskell.packages.${haskellCompiler}.callCabal2nix "axii" ./axii {};

  formalization = pkgs.stdenv.mkDerivation
  {
    name = "Axi";

    meta = with pkgs.lib;
    {
      license = licenses.asl20;
      platforms = platforms.all;
    };

    enableParallelBuilding = true;

    src = pkgs.lib.cleanSource ./Formalization;

    buildInputs = with pkgs;
    [
      coq_9_1
      rocqPackages_9_1.stdlib
    ];

    buildPhase =
    ''
      patchShebangs ./build.sh
      ./build.sh
    '';

    installPhase =
    ''
      INSTALLPATH=$out/lib/coq/${pkgs.coq_9_1.coq-version}/user-contrib/Axi

      mkdir -p $INSTALLPATH
      find . -name "*.v" -o -name "*.vo" -o -name "*.glob" | xargs cp --parents -t $INSTALLPATH/
    '';
  };

  theory = pkgs.stdenv.mkDerivation
  {
    name = "Axi";

    meta = with pkgs.lib;
    {
      license = licenses.asl20;
      platforms = platforms.all;
    };

    src = pkgs.lib.cleanSource ./Theory;

    buildInputs =
    [
      (pkgs.texlive.combine
      {
        inherit (pkgs.texlive) scheme-basic latexmk beamer;
      })
    ];

    buildPhase =
    ''
      patchShebangs ./build.sh
      ./build.sh
    '';

    installPhase =
    ''
      INSTALLPATH=$out/share/theory/

      mkdir -p $INSTALLPATH
      cp *.pdf $INSTALLPATH/
    '';
  };

  vscode-extension = pkgs.vscode-utils.buildVscodeExtension
  {
    pname = "axi-syntax-highlighting";
    version = "0.1.0";

    vscodeExtPublisher = "pevnik-labs";
    vscodeExtName = "axi-syntax-highlighting";
    vscodeExtUniqueId = "pevnik-labs.axi-syntax-highlighting";

    meta = with pkgs.lib;
    {
      description = "Axi syntax highlighting for VSCode";
      license = licenses.asl20;
      platforms = platforms.all;
    };

    src = ./vscode-axi;

    unpackPhase =
    ''
      cp -r $src extension
      chmod -R u+w extension
      sourceRoot=extension
    '';
  };

  tree-sitter-grammar = pkgs.stdenv.mkDerivation
  {
    pname = "tree-sitter-axi";
    version = "0.1.0";

    meta = with pkgs.lib;
    {
      description = "A tree-sitter grammar for Axi.";
      license = licenses.asl20;
      platforms = platforms.all;
    };

    src = ./tree-sitter-axi;

    buildInputs = with pkgs;
    [
      tree-sitter
      emscripten
      nodejs
    ];

    buildPhase =
    ''
      export HOME=$(mktemp -d)
      tree-sitter generate
      tree-sitter build
      tree-sitter build --wasm
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
  };

  all = pkgs.symlinkJoin
  {
    name = "Axi";

    paths =
    [
      prototype
      formalization
      theory
      vscode-extension
      tree-sitter-grammar
    ];
  };

in
{
  inherit prototype formalization theory vscode-extension tree-sitter-grammar all;

  default = all;
}
