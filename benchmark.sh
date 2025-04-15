#!/bin/sh
# Call this script with argument "simple" or "robust"
python3 -m benchexec.benchexec "comparison_$1.xml" --numOfThreads 32
PYTHONPATH=$(pwd) python3 $(which table-generator) $(ls results/* | grep ".*results.[^.]*\.xml.bz2")  --all-columns -x benchmarks/tablegenerator.xml -o results/
