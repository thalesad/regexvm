default: pdf

pdf:
	lhs2TeX report.lhs > report.tex
	pdflatex -shell-escape report
	pdflatex -shell-escape report
	bibtex report
	pdflatex -shell-escape report
