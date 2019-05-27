### Makefile for compiling .tex files ###

#All targets
DOCS = Proposal.pdf Plan.pdf Report.pdf
SRCS = $(wildcard *.tex) lit.bib $(wildcard include/*.tex) $(patsubst agda/%.lagda,latex/%.tex,$(AGDS))
DOTS = $(patsubst %.dot,%.svg,$(wildcard figure/dots/*.dot))
IMGS = $(patsubst %.svg,%.pdf,$(wildcard figure/*.svg) $(DOTS))
AGDS = $(wildcard agda/*.lagda)

#Fail silently
MAKEFLAGS = --silent

xelatex=xelatex -interaction=nonstopmode

default: Report.pdf

docs: $(DOTS) $(IMGS) $(DOCS) force

docs-dbg: $(DOTS) $(IMGS) $(DOCS)

no-imgs: $(DOCS)

figure/%.pdf: figure/%.svg
	convert $^ $@

figure/dots/%.svg: figure/dots/%.dot
	dot -Tsvg $^ > figure/dots/$*.svg

Report.bbl : %.bbl : $(SRCS)
	- $(xelatex) $*.tex
	- bibtex $*

Report.pdf : %.pdf : Report.bbl
	- $(xelatex) $*.tex
	- $(xelatex) $*.tex

%.pdf: $(SRCS)
	- $(xelatex) $*.tex
	- bibtex $*
	- $(xelatex) $*.tex
	- $(xelatex) $*.tex

agda/latex/%.tex : agda/%.lagda
	agda --latex --latex-dir=agda/latex -i agda $<

latex/%.tex : agda/latex/%.tex
	sed -e 's/{code}/{agdacode}/g' < $< > $@

#Remove all temporary files created by pdfLaTeX
clean:
	- rm *.pdf 2> /dev/null
	- rm *.lof *.lot *.out *.toc *.aux *.bbl *.blg *.log 2> /dev/null
	- rm figure/*.pdf 2> /dev/null
	- rm figure/dots/*.pdf figure/dots/*.svg 2> /dev/null

force:
