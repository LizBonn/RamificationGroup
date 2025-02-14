.DEFAULT_GOAL := all

PROJECT = RamificationGroup

.PHONY: all build blueprint blueprint-dev analyze

all : build blueprint

build:
	(lake exe cache get && lake build)

build-print:
	(cd blueprint && mkdir -p print && cd src && xelatex -output-directory=../print print.tex)
	(cd blueprint/print && BIBINPUTS=../src bibtex print.aux)
	(cd blueprint/src && xelatex -output-directory=../print print.tex)
	(cd blueprint/src && xelatex -output-directory=../print print.tex)
	(cp blueprint/print/print.bbl blueprint/src/web.bbl)

build-web:
	(cd blueprint/src && poetry run plastex -c plastex.cfg web.tex)

blueprint: build build-print build-web
	(lake -Kenv=dev update doc-gen4 -R && lake -Kenv=dev build $(PROJECT):docs)
	(cd blueprint && cp -r ../.lake/build/doc ./web/)

blueprint-dev: build-print build-web
	(cd blueprint/web && poetry run python -m http.server)

analyze:
	(poetry run python3 blueprint/blueprint_auto.py -p ${PROJECT})
