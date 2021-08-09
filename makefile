setup:
	pip install pipenv
	pipenv sync
	pipenv shell

dev:
	pip install pipenv
	pipenv sync --dev
	pipenv shell

run:
	python src/ins-json.py
	$(foreach file, $(wildcard ins/*.json), minizinc --solver Gecode src/m1.mzn ins/ins-$(subst ins/ins-,,$(subst .json,,${file})).json -o out/out-$(subst ins/ins-,,$(subst .json,,${file})).txt --soln-sep "" --search-complete-msg "" --solver-time-limit 300000;)
	rm ins/*.json
	python src/printer.py

BRANCH := $(shell git rev-parse --abbrev-ref HEAD)

ifneq (,$(findstring release-,$(BRANCH)))
VERSION := $(subst release-,,$(BRANCH))
else ifneq (,$(findstring hotfix-,$(BRANCH)))
VERSION := $(subst hotfix-,,$(BRANCH))
endif

bump:
	#sed -i '' 's/__version__ = .*/__version__ = '\'$(VERSION)\''/' **/*.py
	#autopep8 -i -a -a **.*py
	#pdoc -o ./docs --docformat numpy very-large-scale-integration
	pipenv lock
	git add .
	git commit -m "Bump version number to $(VERSION)"
	git checkout master
	git merge $(BRANCH)
	git tag $(VERSION)
	git checkout develop
	git merge $(BRANCH)
	git branch -d $(BRANCH)