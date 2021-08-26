setup:
	pip install pipenv
	pipenv sync
	pipenv shell

dev:
	pip install pipenv
	pipenv sync --dev
	pipenv shell

BRANCH := $(shell git rev-parse --abbrev-ref HEAD)

ifneq (,$(findstring release-,$(BRANCH)))
VERSION := $(subst release-,,$(BRANCH))
else ifneq (,$(findstring hotfix-,$(BRANCH)))
VERSION := $(subst hotfix-,,$(BRANCH))
endif

bump:
	sed -i '' 's/__version__ = .*/__version__ = '\'$(VERSION)\''/' *.py
	sed -i '' 's/__version__ = .*/__version__ = '\'$(VERSION)\''/' **/*.py
	autopep8 -i -a -a **/*.py
	sed -i '' 's/from minizinc import Instance, Status/# from minizinc import Instance, Status/' vlsi/utilities/wrappers.py
	pdoc -o ./docs --docformat numpy vlsi
	sed -i '' 's/# from minizinc import Instance, Status/from minizinc import Instance, Status/' vlsi/utilities/wrappers.py
	pipenv lock
	git add .
	git commit -m "Bump version number to $(VERSION)"
	git checkout master
	git merge $(BRANCH)
	git tag $(VERSION)
	git checkout develop
	git merge $(BRANCH)
	git branch -d $(BRANCH)