{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell {
  name = "texlive-env";

  buildInputs = with pkgs; [
    (texlive.combine
      { inherit (texlive)
          scheme-small xdvi;
      })
  ];
}




