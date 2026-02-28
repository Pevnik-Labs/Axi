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

  slides = pkgs.stdenv.mkDerivation
  {
    name = "Axi";

    src = pkgs.lib.cleanSource ./Slides;

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
      INSTALLPATH=$out/share/slides/

      mkdir -p $INSTALLPATH
      cp *.pdf $INSTALLPATH/
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
      slides
    ];
  };

in
{
  inherit prototype formalization theory slides all;

  default = all;
}
