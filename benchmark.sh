#!/bin/sh
rm -rf results
mkdir results
python3 -m benchexec.benchexec comparison.xml --numOfThreads 32
PYTHONPATH=$(pwd) python3 $(which table-generator) results/*xml.bz2  --all-columns -x tablegenerator.xml -o results/
