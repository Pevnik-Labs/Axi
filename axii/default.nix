{ nixpkgs ? import <nixpkgs> {}, compiler ? "ghc984" }:
nixpkgs.pkgs.haskell.packages.${compiler}.callCabal2nix "axii" ./. { }
