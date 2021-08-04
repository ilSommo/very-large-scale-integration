#!/bin/bash

sed -i '' 's/__version__ = .*/__version__ = '\'$1\''/' **/*.py

#autopep8 -i -a -a **.*py

#pdoc -o ./docs --docformat numpy very-large-scale-integration

pipenv lock

git add .
git commit -m "Bump version number to "$1""
git checkout master
git merge release-$1
git tag $1
git checkout develop
git merge release-$1
git branch -d release-$1