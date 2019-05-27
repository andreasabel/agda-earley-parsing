### Makefile for compiling .tex files ###

#All targets
DOCS = Proposal.pdf Plan.pdf Report.pdf
SRCS = $(wildcard *.tex) lit.bib
DOTS = $(patsubst %.dot,%.svg,$(wildcard figure/dots/*.dot))
IMGS = $(patsubst %.svg,%.pdf,$(wildcard figure/*.svg) $(DOTS))

#Fail silently
MAKEFLAGS = --silent

docs: $(DOTS) $(IMGS) $(DOCS) force

docs-dbg: $(DOTS) $(IMGS) $(DOCS)

no-imgs: $(DOCS)

figure/%.pdf: figure/%.svg
	convert $^ $@

figure/dots/%.svg: figure/dots/%.dot
	dot -Tsvg $^ > figure/dots/$*.svg

%.pdf: $(SRCS)
	- xelatex $*.tex
	- bibtex $*
	- xelatex $*.tex
	- xelatex $*.tex

#Remove all temporary files created by pdfLaTeX
clean:
	- rm *.pdf 2> /dev/null
	- rm *.lof *.lot *.out *.toc *.aux *.bbl *.blg *.log 2> /dev/null
	- rm figure/*.pdf 2> /dev/null
	- rm figure/dots/*.pdf figure/dots/*.svg 2> /dev/null

force:
