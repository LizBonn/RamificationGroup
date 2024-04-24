.DEFAULT_GOAL := all

PROJECT = DemoProject

.PHONY: all build blueprint analyze serve

.PHONY: all build blueprint analyze serve

all : build blueprint

build:
	(lake -Kenv=dev exe cache get && lake -Kenv=dev build && lake -Kenv=dev build ${PROJECT}:docs)

blueprint: build
	(cd blueprint && inv all && cp -r ../.lake/build/doc ./web/)

analyze:
	(python3 blueprint/blueprint_auto.py -p ${PROJECT})

serve: blueprint analyze
	(cd blueprint/web && python3 -m http.server)

update:
	lake -Kenv=dev update -R