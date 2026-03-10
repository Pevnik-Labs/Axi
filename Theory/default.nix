{ pkgs ? import <nixpkgs> {} }:

pkgs.stdenv.mkDerivation
{
  name = "Axi";

  meta = with pkgs.lib;
  {
    description = "The metatheory of Axi.";
    license = licenses.asl20;
    platforms = platforms.linux;
  };

  enableParallelBuilding = true;

  src = pkgs.lib.cleanSource ./.;

  nativeBuildInputs =
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
}
