%.tex: %.lagda
	lhs2TeX --agda $< > $@
%.pdf : %.tex
	pdflatex $<
