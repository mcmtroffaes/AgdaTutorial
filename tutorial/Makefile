
DOTS=$(wildcard dot/*.dot)
DOTPNG=$(patsubst dot/%.dot, html/dot/%.gif, $(DOTS))
AGDAPANDOC?=agdapandoc
AGDASTDLIB?=~/share/Agda/lib
HTMLFLAGS?=--html

.PHONY: html clean

html: $(DOTPNG)
	$(AGDAPANDOC) -i $(AGDASTDLIB)/src/ -i src $(HTMLFLAGS) src/Index.lagda --css=Agda.css

clean:
	find . -name "*.agdai" -exec rm -f {} \; 
	find . -name "*~" -exec rm -f {} \; 
	rm -f html/dot/*
	rm -f html/*.html

html/dot/%.gif: dot/%.dot
	dot -Tgif $< -o $@

