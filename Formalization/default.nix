{ pkgs ? import <nixpkgs> {} }:

let
  # When updating Coq versions, just chnge them here.
  coq = pkgs.coq_9_1;
  coqPackages = pkgs.rocqPackages_9_1;
in

pkgs.stdenv.mkDerivation
{
  name = "Axi";

  meta = with pkgs.lib;
  {
    description = "A formalization of Axi's metatheory.";
    license = licenses.asl20;
    platforms = platforms.linux;
  };

  enableParallelBuilding = true;

  src = pkgs.lib.cleanSource ./.;

  nativeBuildInputs =
  [
    coq
    coqPackages.stdlib
  ];

  buildPhase =
  ''
    patchShebangs ./build.sh
    ./build.sh
  '';

  installPhase =
  ''
    INSTALLPATH=$out/lib/coq/${coq.coq-version}/user-contrib/Axi

    mkdir -p $INSTALLPATH
    find . -name "*.v" -o -name "*.vo" -o -name "*.glob" | xargs cp --parents -t $INSTALLPATH/
  '';
}
