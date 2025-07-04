{ nixpkgs ? import <nixpkgs> {}, compiler ? "ghc984" }:
let
  haskellPackages = nixpkgs.pkgs.haskell.packages.${compiler};
in
haskellPackages.shellFor {
  packages = hpkgs: [
    # reuse the nixpkgs for this package
    hpkgs.distribution-nixpkgs
    # call our generated Nix expression manually
    (hpkgs.callCabal2nix "axii" ./. { })
    # haskell dev tools
    hpkgs.alex
    hpkgs.happy
  ];

  # development tools we use
  nativeBuildInputs = [
    haskellPackages.alex
    haskellPackages.BNFC
    haskellPackages.cabal-install
    haskellPackages.happy
    haskellPackages.haskell-language-server
    haskellPackages.hpack
  ];

  # Extra arguments are added to mkDerivation's arguments as-is.
  # Since it adds all passed arguments to the shell environment,
  # we can use this to set the environment variable the `Paths_`
  # module of distribution-nixpkgs uses to search for bundled
  # files.
  # See also: https://cabal.readthedocs.io/en/latest/cabal-package.html#accessing-data-files-from-package-code
  distribution_nixpkgs_datadir = toString ./distribution-nixpkgs;
}
