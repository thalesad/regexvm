default: pdf

pdf:
	coqdoc --latex --no-preamble --parse-comments -s -o paper.tex paper.v
	pdflatex --shell-escape regexvm.tex
	pdflatex --shell-escape regexvm.tex
	bibtex regexvm
	pdflatex --shell-escape regexvm.tex
