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
VERSION := $(subst release-,, $(BRANCH))
else ifneq (,$(findstring hotfix-,$(BRANCH)))
VERSION := $(subst hotfix-,, $(BRANCH))
endif

bump:
<<<<<<< HEAD
=======
	#sed -i '' 's/__version__ = .*/__version__ = '\'$(VERSION)\''/' **/*.py
	#autopep8 -i -a -a **.*py
	#pdoc -o ./docs --docformat numpy very-large-scale-integration
>>>>>>> release-0.1.1
	pipenv lock
	git add .
	git commit -m "Bump version number to $(VERSION)"
	git checkout master
	git merge $(BRANCH)
	git tag $(VERSION)
	git checkout develop
	git merge $(BRANCH)
	git branch -d $(BRANCH)