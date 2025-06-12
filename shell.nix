{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell {
  name = "texlive-env";

  buildInputs = with pkgs; [
    entr
    (texlive.combine
      { inherit (texlive)
          acmart
          latexmk
          scheme-small
          xdvi

          # acmart dependencies
          amscls
          amsfonts
          amsmath
          # binhex
          booktabs
          caption
          comment
          cm-super
          cmap
          doclicense
          draftwatermark
          environ
          etoolbox
          fancyhdr
          float
          fontaxes
          geometry
          graphics
          hyperref
          hyperxmp
          ifmtarg
          iftex
          inconsolata
          libertine
          # manyfoot
          microtype
          mmap
          # ms
          mweights
          natbib
          # nccfoots
          ncctools # provide manyfoot
          newtx
          oberdiek
          # pdftex-def
          preprint # provides: balance
          refcount
          setspace
          textcase
          totpages
          trimspaces
          upquote
          url
          xcolor
          xkeyval
          xstring;
      })
  ];
}




