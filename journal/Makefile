%.tex: %.lagda
	lhs2tex --agda $< > $@
%.pdf : %.tex
	pdflatex $<
