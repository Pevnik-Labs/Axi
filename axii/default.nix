{ pkgs ? import <nixpkgs> {}, compiler ? "ghc984" }:

pkgs.haskell.packages.${compiler}.callCabal2nix "axii" ./. { }
