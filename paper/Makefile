.SUFFIXES: .tex .bib .aux .bbl .dvi .ps .pdf

all:	oopsla.pdf

oopsla.pdf:	oopsla.bbl
	pdflatex oopsla
	pdflatex oopsla

oopsla.bbl:	references.bib oopsla.aux
	bibtex oopsla

oopsla.aux:	*.tex
	pdflatex oopsla

clean:
	rm -f *.{log,aux,out,bbl,blg,dvi,ps,pdf}
