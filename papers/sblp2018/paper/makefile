default: pdf

pdf:
	lhs2TeX paper.lhs > paper.tex
	pdflatex paper
	pdflatex paper
	bibtex paper
	pdflatex paper
