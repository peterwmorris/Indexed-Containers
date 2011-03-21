paper.tex: paper.lagda tt.lagda cont.lagda ifunc.lagda icont.lagda initalg.lagda termcoalg.lagda wifromw.lagda mfromw.lagda
	lhs2TeX --agda paper.lagda > paper.tex
%.pdf : %.tex
	pdflatex $<
