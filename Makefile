
# workflow: SRC -- agda --> TMP 1 -- PP --> TMP 2 -- pandoc --> TMP 3 --> OUT (final markdown) --> Jekyll _site (HTML)

OUTDIR := html
TMPDIR := tmp
SITEDIR := _site
DOCSDIR := docs
SRCDIR := src
BUILDDIR := $(SRCDIR)/_build
INCLUDES := _includes
SVGS := $(INCLUDES)/svgs
PARTS := Preliminaries General Special
LIBRARYPARTS := Agda Data Function Relation
AGDA := agda
# PP := /usr/local/bin/pp
# PP := ~/.local/bin/pp
PP := ./pp/pp-macos
# PP := /home/pi/.local/bin/pp
EPUBCHECK := epubcheck
RUBY := ruby
GEM := $(RUBY) -S gem
BUNDLE := $(RUBY) -S bundle
JEKYLL := $(BUNDLE) exec jekyll
HTMLPROOFER := $(BUNDLE) exec htmlproofer
#FIX_LINKS := $(TMP)/fix-links.sed
ASPELL = aspell
SED := sed -i ""
# SED := sed -i
GSED := gsed
# GSED := sed
STAT := stat -f "%Sm"
# STAT := stat -c "%y"

# the citation style
CSL := natbib.csl

# the bibliography file
BIB := bibliography.bib

#--filter=pandoc-crossref
#ifneq ($(shell pandoc --version | head -n1 | egrep "pandoc 2\.11\.." ),)
# more recent pandoc versions embed the citeproc library
PANDOCEXEC := pandoc --citeproc
#else
#	PANDOCEXEC := pandoc --filter=pandoc-citeproc
#endif

PANDOC := $(PANDOCEXEC) --filter=pandoc-numbering --bibliography=$(BIB) --csl=$(CSL) --metadata link-citations=true --from markdown --to markdown_phpextra

AGDA_SOURCES := $(shell find $(SRCDIR) -name '*.lagda.md' -and -not -name '.\#*')
#$(info AGDA_SOURCES:$(AGDA_SOURCES))

AGDA_MODULES := $(patsubst %.lagda.md,%,$(notdir $(AGDA_SOURCES)))
#$(info AGDA_MODULES:$(AGDA_MODULES))

#AGDA_TMPS := $(foreach PART,$(PARTS),$(foreach AGDA_MODULE,$(AGDA_MODULES),$(TMPDIR)/$(PART).$(AGDA_MODULE).md))
#$(info AGDA_TMPS:$(AGDA_TMPS))

#AGDA_DEPS := $(patsubst %,%.dep,$(AGDA_TMPS))
#$(info AGDA_DEPS:$(AGDA_DEPS))

#AGDA_MD := $(patsubst $(SRCDIR)/%.lagda.md,$(OUTDIR)/%.md,$(AGDA_SOURCES))
#$(info AGDA_MD:$(AGDA_MD))

MARKDOWN_SOURCES := $(shell find $(SRCDIR) -name '*.md' -and -not -name '*.lagda.md' -and -not -name '*\#*' -and -not -name 'footer.md')
$(info MARKDOWN_SOURCES:$(MARKDOWN_SOURCES))

MARKDOWN_MD := $(patsubst $(SRCDIR)/%.md,$(OUTDIR)/%.md,$(MARKDOWN_SOURCES))
$(info MARKDOWN_MD:$(MARKDOWN_MD))

PART_DIRS := $(patsubst %,$(OUTDIR)/%,$(PARTS))
#$(info PART_DIRS:$(PART_DIRS))

.PHONY: all build agda markdown serve server-start server-stop clean keys refs spellcheck docs

#$(TMPDIR)/all.dep.txt $(TMPDIR)/keys.dep.txt $(TMPDIR)/all_keys.dep.txt

all: build
	
docs: build
	rm -fr $(DOCSDIR)/ && rsync -aP $(SITEDIR)/ $(DOCSDIR)/

clean:
	@rm -fr keys.make $(OUTDIR)/ $(TMPDIR)/ $(SITEDIR)/ $(BUILDDIR)/ $(SVGS)/ $(DOCSDIR)/

markdown: agda refs $(MARKDOWN_MD)

spellcheck:
	@echo " [DONE]"

$(OUTDIR):
	@mkdir -p $(OUTDIR)

check: build
	$(HTMLPROOFER) ./_site

build: markdown
	$(JEKYLL) build --incremental --trace

# Start Jekyll server with --incremental
serve: markdown
	$(JEKYLL) serve --incremental
#pkill -f fswatch

watch:
	fswatch -o ./src | xargs -n1 -I{} make agda2

# Start detached Jekyll server
server-start:
	$(JEKYLL) serve --incremental --no-watch --detach

# Stop detached Jekyll server
server-stop:
	pkill -f jekyll

# special treatment for the index
agda: $(OUTDIR) $(OUTDIR)/index.md

$(OUTDIR)/index.md: $(SRCDIR)/index.md
	@echo "$(SRCDIR)/index.md --> $(OUTDIR)/index.md\c"

	@$(PANDOC) $(SRCDIR)/index.md -o $(OUTDIR)/index.md

	$(eval LAST_MODIFIED := $(shell $(STAT) $(SRCDIR)/index.md))

	@$(GSED) -i "1i---" $(OUTDIR)/index.md
	@$(GSED) -i "2ititle : Table of Contents" $(OUTDIR)/index.md
	@$(GSED) -i "3ilayout : home" $(OUTDIR)/index.md
	@$(GSED) -i "4ilast-modified: $(LAST_MODIFIED)" $(OUTDIR)/index.md
	@$(GSED) -i "5ipermalink: /" $(OUTDIR)/index.md
	@$(GSED) -i "6i---" $(OUTDIR)/index.md
#	@$(SED) -i "6i " $(OUTDIR)/index.md

	@echo " [DONE]"

keys_exist := $(wildcard $(TMPDIR)/keys.dep.txt)

ifneq ($(strip $(keys_exist)),)

# if keys.dep.txt already exists, then use it to generate refs dependencies;
# it is convenient to have this rule when running "make clean"
# (otherwise it will try to build keys.dep.txt every time...)

else

# generate the code above dynamically if keys.dep.txt does not exists yet
-include keys.make

endif

keys.make: Makefile $(TMPDIR)/keys.dep.txt

	@echo "making $@...\c"

	@printf 'REFS := $$(shell cat $$(TMPDIR)/keys.dep.txt)\n' > $@
	@printf '$$(foreach REF,$$(REFS),$$(eval $$(call process_refs,$$(word 1,$$(subst ., ,$$(REF))),$$(word 2,$$(subst ., ,$$(REF))),$$(word 3,$$(subst ., ,$$(REF))),$$(word 4,$$(subst ., ,$$(REF))),$$(word 5,$$(subst ., ,$$(REF))))))' >> $@

	@echo " [DONE]"

define add_dependency

$(TMPDIR)/$1.$2.md: $(SRCDIR)/$1/$2.lagda.md
	@echo "$(SRCDIR)/$1/$2.lagda.md --> $(TMPDIR)/$1.$2.md\c"

	@cd $(SRCDIR) && $(AGDA) --library-file=../.agda/libraries --html --html-highlight=code --html-dir=../$(TMPDIR) "$1/$2.lagda.md" | \
		sed '/^Generating.*/d; /^Warning\: HTML.*/d; /^reached from the.*/d; /.*Checking.*/d' | \
		tr -d '\n'

	@echo " [DONE]"

# dummy output
$(TMPDIR)/$1.$2.lagda.md.spellcheckme: $(SRCDIR)/$1/$2.lagda.md
#	@cat $(SRCDIR)/$1/$2.lagda.md | sed "s|@[^@]*||g" > $(TMPDIR)/$1.$2.lagda.md.spellcheckme
	@$(ASPELL) --home-dir=spell-checker/ --lang=en_GB --mode=markdown --add-filter url --add-filter url --add-filter tex -c $(SRCDIR)/$1/$2.lagda.md
	@printf .

spellcheck: $(TMPDIR)/$1.$2.lagda.md.spellcheckme
.PHONY: $(TMPDIR)/$1.$2.lagda.md.spellcheckme

# don't do deps
$(TMPDIR)/$1.$2.md.dep: $(TMPDIR)/$1.$2.md
	@echo "$(TMPDIR)/$1.$2.md --> $(TMPDIR)/$1.$2.md.dep\c"

# prepare the source by adding #'s to module names, as follows:
# <a id="37" class="Keyword">module</a> <a id="44" href="part0.Booleans.html" class="Module"> becomes
# <a id="37" class="Keyword">module</a> <a id="44" href="part0.Booleans.html#44" class="Module">
# this is necessary to have also module names appear in the dep file
	@$(SED) 's|<a id="\([0-9]*\)" class="Keyword">module</a> <a id="\([^"]*\)" href="\([a-zA-Z0-9\.]*\)" class="Module">|<a id="\1" class="Keyword">module</a> <a id="\2" href="\3#\2" class="Module">|g' $(TMPDIR)/$1.$2.md

	@./extract_function_names.sh $(TMPDIR) $1.$2.md

# sanitise a bit
# &lt; becomes <
# &gt; becomes >
# &#39; becomes '

#	@$(SED) 's|&lt;|<|g' $(TMPDIR)/$1.$2.md.dep
#	@$(SED) 's|&gt;|>|g' $(TMPDIR)/$1.$2.md.dep
#	@$(SED) "s|&\#39;|'|g" $(TMPDIR)/$1.$2.md.dep
#	@./escape_dollar.sh $(TMPDIR)/$1.$2.md.dep

	@echo " [DONE]"

# MAIN WORKHORSE
$(OUTDIR)/$1/$2.md: $(TMPDIR)/$1.$2.md
	@echo "$(TMPDIR)/$1.$2.md --> $(OUTDIR)/$1/$2.md \c"

	$(eval LAST_MODIFIED := $(shell $(STAT) $(SRCDIR)/$1/$2.lagda.md))

	@mkdir -p $(OUTDIR)/$1

	@cat $(TMPDIR)/$1.$2.md > $(TMPDIR)/$1.$2.1.md

# add the markdown footer
	@cat $(SRCDIR)/footer.md >> $(TMPDIR)/$1.$2.1.md

	@$(GSED) -i "3isrc: $(SRCDIR)/$1/$2.lagda.md" $(TMPDIR)/$1.$2.1.md
	@$(GSED) -i "4ilayout: page" $(TMPDIR)/$1.$2.1.md
	@$(GSED) -i "5ipermalink: /$(1)/$(2)/" $(TMPDIR)/$1.$2.1.md
	@$(GSED) -i "6ilast-modified: $(LAST_MODIFIED)" $(TMPDIR)/$1.$2.1.md
	@$(GSED) -i "7ipart: /$(1)/index/" $(TMPDIR)/$1.$2.1.md
	@$(GSED) -i "8itoc: true" $(TMPDIR)/$1.$2.1.md
	@$(GSED) -i "9inumbersections: true" $(TMPDIR)/$1.$2.1.md
#	@$(GSED) -i "10ipandoc-numbering:" $(TMPDIR)/$1.$2.1.md
#	@$(GSED) -i "11i\    exercise:" $(TMPDIR)/$1.$2.1.md
#	@$(GSED) -i "12i\        general:" $(TMPDIR)/$1.$2.1.md
#	@$(GSED) -i "13i\            listing-title: List of exercises" $(TMPDIR)/$1.$2.1.md
#	@$(GSED) -i "14i\            listing-identifier: False" $(TMPDIR)/$1.$2.1.md

# WARNING: the number of added lines will affect the following!

	@echo "1 \c"
# STEP 0: apply PP macros

ifneq ($(wildcard $(SRCDIR)/$1/$2.pp),)
# additionally import a chapter-specific pp macrofile, if it exists
	@$(PP) -import=macros.pp -import=$(SRCDIR)/$1/$2.pp -D part=$1 -D chapter=$2 $(TMPDIR)/$1.$2.1.md > $(TMPDIR)/$1.$2.2.md
else
	@$(PP) -import=macros.pp -D part=$1 -D chapter=$2 $(TMPDIR)/$1.$2.1.md > $(TMPDIR)/$1.$2.2.md
endif
	@echo "2 \c"

# 2>/dev/null || true

# STEP 1: process citations
# Table of contents shows up only with options "--from markdown --to markdown_phpextra"
	@$(PANDOC) $(TMPDIR)/$1.$2.2.md -o $(TMPDIR)/$1.$2.3.md

# sometimes pandoc transforms <pre class="Agda"> to <pre markdown="1" class="Agda">, we need to undo this 
	@$(SED) 's|<pre markdown="1" class="Agda">|<pre class="Agda">|g' $(TMPDIR)/$1.$2.3.md

# sometimes pandoc adds section references such as {#an-unreferenced-section .unnumbered}, but we need to remove .unnumbered
	@$(SED) 's| .unnumbered||g' $(TMPDIR)/$1.$2.3.md
	@echo "3 \c"

# re-copy the headers
	@head -n11 $(TMPDIR)/$1.$2.1.md > $(OUTDIR)/$1/$2.md

# add an horizontal separator
#	@echo "\n\n---\n\n" >> $(OUTDIR)/$1/$2.md

	@cat $(TMPDIR)/$1.$2.3.md >> $(OUTDIR)/$1/$2.md

#	@cp -f $(TMPDIR)/$1.$2.md $(OUTDIR)/$1/$2.md

	@$(SED) 's|<pre class="Agda">|{% raw %}<pre class="Agda">|g' $(OUTDIR)/$1/$2.md
	@$(SED) 's|<pre data-executable|{% raw %}<pre data-executable|g' $(OUTDIR)/$1/$2.md
#	@$(SED) 's|<pre|{% raw %}<pre|g' $(OUTDIR)/$1/$2.md

	@$(SED) 's|</pre>|</pre>{% endraw %}|g' $(OUTDIR)/$1/$2.md

# this removes the newline before </pre>, 
# additionally remove the newline between </a> and </pre> (useful for formatting) in inline code
	@./scripts/fix_newlines.sh $(OUTDIR)/$1/$2.md
	@./scripts/fix_newlines.sh $(OUTDIR)/$1/$2.md
	@./scripts/fix_newlines.sh $(OUTDIR)/$1/$2.md

#	cp $(OUTDIR)/$1/$2.md $(OUTDIR)/$1/$2.md.sed


#{% include markdown_file.md %}

# change the href link in those positions where names are first declared;
# this is achieved by matching on positions as below
# <a id="𝔹"></a><a id="200" href="part0.Booleans.html#200"

#IGNORE FOR NOW
#	@$(SED) 's|<a id="\([^"]*\)"></a><a id="\([0-9]*\)" href="\([a-zA-Z0-9\.]*\)\#[0-9]*"|<a id="\1"></a><a id="\2" href="{% endraw %}{% link '$(OUTDIR)/refs/$1/$2/'index.md %}#ref-\2{% raw %}"|g' $(OUTDIR)/$1/$2.md

# do the same for modules, we now match on things like
# <a id="37" class="Keyword">module</a> <a id="44" href="part0.Booleans.html" class="Module"> or
# <a id="113" class="Keyword">module</a> <a id="120" href="part1.Hilbert.html#120" class="Module">part1.Hilbert</a>

#IGNORE FOR NOW
#	@$(SED) 's|<a id="\([^"]*\)" class="Keyword">module</a> <a id="\([^"]*\)" href="[^"]*" class="Module">|<a id="\1" class="Keyword">module</a> <a id="\2" href="{% endraw %}{% link '$(OUTDIR)/refs/$1/$2/'index.md %}{% raw %}" class="Module">|g' $(OUTDIR)/$1/$2.md

# this is just for debugging to see the intermediate result
#	@cp $(OUTDIR)/$1/$2.md $(OUTDIR)/$1/$2.md.txt

#	@$(GSED) -i "3isrc: $(SRCDIR)/$1/$2.lagda.md" $(OUTDIR)/$1/$2.md
#	@$(GSED) -i "4ilayout: page" $(OUTDIR)/$1/$2.md
#	@$(GSED) -i "5ipermalink: /$(1)/$(2)/" $(OUTDIR)/$1/$2.md
#	@$(GSED) -i "6ilast-modified: $(LAST_MODIFIED)" $(OUTDIR)/$1/$2.md
#	@$(GSED) -i "7ipart: /$(1)/index/" $(OUTDIR)/$1/$2.md
#	@$(GSED) -i "8itoc: true" $(OUTDIR)/$1/$2.md
#	@$(GSED) -i "9inumbersections: true" $(OUTDIR)/$1/$2.md
#	@$(GSED) -i "10ipandoc-numbering:" $(OUTDIR)/$1/$2.md
#	@$(GED) -i "11i\    exercise:" $(OUTDIR)/$1/$2.md
#	@$(GED) -i "12i\        general:" $(OUTDIR)/$1/$2.md
#	@$(GED) -i "13i\            listing-title: List of exercises" $(OUTDIR)/$1/$2.md

#{{ site.baseurl }}

# fix the links in place: $(PART).$(AGDA_MODULE).html --> $(OUTDIR)/$(PART)/$(AGDA_MODULE).md
	@$(foreach PART,$(PARTS),$(foreach AGDA_MODULE,$(AGDA_MODULES),$(SED) 's+$(PART).$(AGDA_MODULE).html+{% endraw %}{{ site.baseurl }}{% link $(OUTDIR)/$(PART)/$(AGDA_MODULE).md %}{% raw %}+g;' $(OUTDIR)/$1/$2.md;))

# TODO: fix the links to the agda library
# example: 'href="Relation..."' --> 'href="https://agda.github.io/agda-stdlib/v2.3/Relation..."'

#string='This is a sample 123 text and some 987 numbers'
#echo "$string" | sed -rn 's/[^[:digit:]]*([[:digit:]]+)[^[:digit:]]+([[:digit:]]+)[^[:digit:]]*/\1 \2/p'
#echo 'aaa href="Data.Int.html"' | sed 's+href="\(Data..*.html\)"+"href="ciao/\1"+g'

	@$(foreach PART,$(LIBRARYPARTS),$(SED) 's+href="\($(PART).[^"]*.html\)+href="https://agda.github.io/agda-stdlib/v2.3/\1+g;' $(OUTDIR)/$1/$2.md;)

	@echo " [DONE]"

agda: $(OUTDIR)/$1/$2.md

endef

$(foreach SOURCE,$(AGDA_SOURCES),$(eval $(call add_dependency,$(word 2,$(subst /, ,$(SOURCE))),$(word 1,$(subst ., ,$(word 3,$(subst /, ,$(SOURCE))))))))

agda2:
	make agda
	make agda
