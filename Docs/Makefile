### Makefile for compiling .tex files ###

#All targets
DOCS = Proposal.pdf Plan.pdf Report.pdf
SRCS = $(wildcard *.tex) lit.bib $(wildcard include/*.tex) $(LTXS) #$(patsubst agda/%.lagda,latex/%.tex,$(AGDS))
DOTS = $(patsubst %.dot,%.svg,$(wildcard figure/dots/*.dot))
IMGS = $(patsubst %.svg,%.pdf,$(wildcard figure/*.svg) $(DOTS))
AGDS = $(wildcard agda/*.lagda)
LTXS = $(patsubst include/%,latex/%,$(wildcard include/*.tex))

#Fail silently
#MAKEFLAGS = --silent

xelatex=xelatex -interaction=nonstopmode

# List of goals that should be executed even if there is a file/dir of the same name.
.PHONY: default docs docs-dbg no-imgs clean force

default: Report.pdf

docs: $(DOTS) $(IMGS) $(DOCS) force

docs-dbg: $(DOTS) $(IMGS) $(DOCS)

no-imgs: $(DOCS)

figure/%.pdf: figure/%.svg
	convert $^ $@

figure/dots/%.svg: figure/dots/%.dot
	dot -Tsvg $^ > figure/dots/$*.svg

Report.bbl : %.bbl : agda/latex $(SRCS) latex/agda.sty
	- $(xelatex) $*.tex
	- bibtex $*

Report.pdf : %.pdf : Report.bbl
	- $(xelatex) $*.tex
	- $(xelatex) $*.tex

agda/latex:
	mkdir -p agda/latex
	mkdir -p latex

latex/agda.sty : latex latex-agda.sty
	cp latex-agda.sty latex/agda.sty

%.pdf: $(SRCS)
	- $(xelatex) $*.tex
	- bibtex $*
	- $(xelatex) $*.tex
	- $(xelatex) $*.tex

# Try to apply Agda formatting.  If it fails, use plain copy.
latex/%.tex : include/%.tex
	cp $< $@
	sed -e 's/\t//g' < $< > agda/$*.lagda
	- agda --latex --latex-dir=agda/latex -i agda agda/$*.lagda && sed -e 's/{code}/{agdacode}/g' < agda/latex/$*.tex > $@

# Individual rules:

# agda/%.lagda : include/%.tex
# 	sed -e 's/\t//g' include/$*.tex > agda/$*.lagda

# agda/latex/%.tex : agda/%.lagda
# 	- agda --latex --latex-dir=agda/latex -i agda agda/$*.lagda

# latex/%.tex : agda/latex/%.tex
# 	- sed -e 's/{code}/{agdacode}/g' < $< > $@

#Remove all temporary files created by pdfLaTeX
clean:
	- rm *.pdf 2> /dev/null
	- rm *.lof *.lot *.out *.toc *.aux *.bbl *.blg *.log 2> /dev/null
	- rm figure/*.pdf 2> /dev/null
	- rm figure/dots/*.pdf figure/dots/*.svg 2> /dev/null
	- rm -R agda latex 2> /dev/null

force:
