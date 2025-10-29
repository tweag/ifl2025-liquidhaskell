## The output directory
OUTPUT_DIR=$(shell pwd)/dist

LATEX=latexmk -pdflatex -shell-escape -output-directory=$(OUTPUT_DIR) -halt-on-error -interaction=nonstopmode
LATEX_SRC=main.tex references.bib

all: main

## Standard cleanup
clean:
	rm -rf $(OUTPUT_DIR)/*

main : $(LATEX_SRC)
	$(LATEX) main.tex

continuous::
	ls $(LATEX_SRC) Makefile | entr make -j
