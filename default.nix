{ pkgs ? import <nixpkgs> {} }:

let
  # The Haskell prototype's build is managed by Cabal.
  haskellCompiler = "ghc984";
  prototype = pkgs.haskell.packages.${haskellCompiler}.callCabal2nix "axii" ./axii {};

  formalization = pkgs.stdenv.mkDerivation
  {
    name = "Axi";

    src = pkgs.lib.cleanSource ./Formalization;

    enableParallelBuilding = true;

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
      cp -r * $INSTALLPATH/

      # Remove .vos, .vok and .aux files.
      find $INSTALLPATH -name "*.vos" -o -name "*.vok" -o -name ".*.aux" | xargs rm -f
    '';
  };

  theory = pkgs.stdenv.mkDerivation
  {
    name = "Axi";

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
      license = licenses.isc;
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

  all = pkgs.symlinkJoin
  {
    name = "Axi";

    paths =
    [
      prototype
      formalization
      theory
      vscode-extension
    ];
  };

in
{
  inherit prototype formalization theory vscode-extension all;

  default = all;
}
