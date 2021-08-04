setup:
	pip install pipenv
	pipenv sync
	pipenv shell

dev:
	pip install pipenv
	pipenv sync --dev
	pipenv shell