## The output directory
OUTPUT_DIR=$(shell pwd)/dist

LATEX=latexmk -xelatex -shell-escape -output-directory=$(OUTPUT_DIR)

all: main

## Standard cleanup
clean:
	rm -rf $(OUTPUT_DIR)/*

main : main.tex references.bib
	$(LATEX) main.tex
