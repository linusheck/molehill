# <img src="resources/molehill.svg" alt="Molehill Logo" height="25"/> Molehill Markov chain searcher 

## Installation

We currently use `setuptools` because I can't find another way to install `stormpy`, but that might change soon.
Create a virtualenv, e.g., with pipenv:
```
pipenv shell
```
and install `requirements.txt`:
```
pip install -r requirements.txt
```

## Storm setup

Install Storm. Currently, I can't keep `stormpy` from asking the CMake Cache for the location of Storm. So please check your
```
~/.cmake/packages/storm/<UUID>
~/.cmake/packages/carl/<UUID>
```
and make sure you have one file in this folder that points to the Storm you want `stormpy` to compile against. Sorry, I'll fix this soon.
Then run setup.py
```
python setup.py install
```
which will (hopefully) build and install `pycarl`, `stormpy`, `PAYNT`, and finally `fastmole` and `molehill`.

## Run molehill

For help, execute
```
python -m molehill --help
```