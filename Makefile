
DOTS=$(wildcard dot/*.dot)
DOTPNG=$(patsubst dot/%.dot, html/dot/%.gif, $(DOTS))

.PHONY: html sync

html: $(DOTPNG)
	agda -i ~/Agda/lib/src/ -i . --html=NoSlides Index.lagda --css=Agda.css
#	agda -i ~/share/Agda/lib/src/ -i . --html=SlidySlides --template=slidy.template Index.lagda --css=Agda.css
#	agda -i ~/share/Agda/lib/src/ -i . --html=S5Slides --template=s5.template Index.lagda --css=Agda.css
#	agda -i ~/share/Agda/lib/src/ -i . --html=DZSlides --template=dz.template Index.lagda --css=Agda.css
#	agda -i ~/share/Agda/lib/src/ -i . --html=SlideousSlides --template=slideous.template Index.lagda --css=Agda.css

html/dot/%.gif: dot/%.dot
	dot -Tgif $< -o $@

