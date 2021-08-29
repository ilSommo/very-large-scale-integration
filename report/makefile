pdf:
	pdflatex --shell-escape report.tex
	pdflatex --shell-escape report.tex

all:
	latexindent report.tex -o report.tex
	pdflatex --shell-escape report.tex
	pdflatex --shell-escape report.tex
	rm *.aux *.lof *.log *.out *.toc
	rm -r _minted-report