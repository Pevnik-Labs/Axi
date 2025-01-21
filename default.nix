{ pkgs ? import <nixpkgs> {} }:

with pkgs;

stdenv.mkDerivation {
  name = "T-Axi";
  buildInputs = [ (texlive.combine {
                    inherit (texlive)
                      scheme-small

                      # Add other LaTeX libraries (packages) here as needed, e.g:
                      # stmaryrd amsmath pgf

                      # build tools
                      latexmk
                      ;
                  })
                  glibcLocales
                ];
  src = ./.;

  meta = with lib; {
    description = "Prototype of typed Axi - docs and implementation";
    license = licenses.isc;
    platforms = platforms.linux;
  };
}
