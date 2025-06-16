{ pkgs ? import (fetchTarball "https://github.com/NixOS/nixpkgs/archive/3e3afe5174c5.tar.gz") {} }:

pkgs.mkShell {
  name = "liquid-rapier-ifl25";

  buildInputs = with pkgs; [
    haskell.compiler.ghc9122
    z3
    git
    cabal-install
  ];
}

