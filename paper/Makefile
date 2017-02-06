.SUFFIXES: .tex .bib .aux .bbl .dvi .ps .pdf

all:	podc.pdf

podc.pdf:	podc.bbl
	pdflatex podc
	pdflatex podc

podc.bbl:	references.bib podc.aux
	bibtex podc

podc.aux:	*.tex
	pdflatex podc

clean:
	rm -f *.{log,aux,out,bbl,blg,dvi,ps,pdf}
