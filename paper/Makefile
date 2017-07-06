.SUFFIXES: .tex .sty .bib .aux .bbl .dvi .ps .pdf .zip

all:	oopsla.pdf

oopsla.pdf:	oopsla.bbl
	pdflatex oopsla
	pdflatex oopsla

oopsla.bbl:	references.bib oopsla.aux
	bibtex oopsla

oopsla.aux:	*.tex
	pdflatex oopsla

# ms.tex is the top-level filename expected by arxiv. See https://arxiv.org/help/submit_tex
ms.tex: oopsla.tex oopsla.bbl
	sed -e '/\\bibliography{references}/ r oopsla.bbl' -e '/\\bibliography{references}/ d' oopsla.tex > ms.tex

arxiv.zip: ms.tex acmart.cls comment.sty isabelle.sty isabellesym.sty isabelletags.sty \
		proof-strategy.tex proof-structure.tex isabelle.tex convergence.tex \
		network.tex rga.tex simple-crdts.tex relwork.tex
	zip $@ $^

clean:
	rm -f *.{log,aux,out,bbl,blg,dvi,ps,pdf} ms.tex arxiv.zip
