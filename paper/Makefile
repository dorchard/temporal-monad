default: main

clean:
	rm -f *._tex
	rm -f *.aux
	rm -f *.bbl
	rm -f *.blg
	rm -f *.dvi
	rm -f *.ptb
	rm -f *.toc

main: 
	lhs2TeX -o paper.tex paper.lhs
	latex paper.tex
	bibtex paper
	pdflatex paper.tex
	pdflatex paper.tex

quick:
	lhs2TeX -o paper.tex paper.lhs
	pdflatex paper.tex

