paper.tex: paper.lagda introduction.lagda tt.lagda cont.lagda ifunc.lagda icont.lagda initalg.lagda termcoalg.lagda wifromw.lagda mfromw.lagda spf.lagda
	lhs2TeX --agda paper.lagda > paper.tex

%.pdf : %.tex
	pdflatex $<

journal : paper.tex
	latex paper.tex
	bibtex paper
	latex paper.tex
	pdflatex paper
