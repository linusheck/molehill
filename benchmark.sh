#!/bin/sh
# Call this script with argument "simple" or "robust" 

RESULT_DIR="results/$1-$(date +"%Y-%m-%d_%H-%M-%S")"
mkdir -p "$RESULT_DIR"

python3 -m benchexec.benchexec "comparison_$1.xml" --numOfThreads $2 --outputpath "$RESULT_DIR"

# RESULT_DIR="stored_results/simple-2025-05-06_14-15-28/"

./plot.sh $RESULT_DIR
