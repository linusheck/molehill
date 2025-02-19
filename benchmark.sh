#!/bin/sh
python3 -m benchexec.benchexec comparison.xml --numOfThreads 32
PYTHONPATH=$(pwd) python3 $(which table-generator) $(ls results/* | grep ".*results.[^.]*\.xml.bz2")  --all-columns -x benchmarks/tablegenerator.xml -o results/
