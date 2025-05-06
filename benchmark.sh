#!/bin/sh
# Call this script with argument "simple" or "robust" 

# Get current datetime in format YYYY-MM-DD_HH-MM-SS
RESULT_DIR="results/$1-$(date +"%Y-%m-%d_%H-%M-%S")"
mkdir -p "$RESULT_DIR"

python3 -m benchexec.benchexec "comparison_$1.xml" --numOfThreads $2 --outputpath "$RESULT_DIR"
PYTHONPATH=$(pwd) python3 $(which table-generator) $(ls $RESULT_DIR/* | grep ".*results.[^.]*\.xml.bz2")  --all-columns -x benchmarks/tablegenerator.xml -o $RESULT_DIR
