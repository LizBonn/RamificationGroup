.DEFAULT_GOAL := all

PROJECT = RamificationGroup

.PHONY: all build blueprint blueprint-dev analyze serve update

all : build blueprint

build:
	(lake -Kenv=dev exe cache get && lake -Kenv=dev build && lake -Kenv=dev build ${PROJECT}:docs)

blueprint: build
	(cd blueprint && inv all && cp -r ../.lake/build/doc ./web/)

blueprint-dev:
	(cd blueprint && inv all)

analyze:
	(python3 blueprint/blueprint_auto.py -p ${PROJECT})

serve: blueprint-dev analyze
	(cd blueprint && inv serve)

update:
	(curl -L https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain -o lean-toolchain && \
		lake -Kenv=dev update -R)