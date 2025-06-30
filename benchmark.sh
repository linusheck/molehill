#!/bin/sh
# Call this script with argument "simple" or "robust" 

RESULT_DIR="results/$1-$(date +"%Y-%m-%d_%H-%M-%S")"
mkdir -p "$RESULT_DIR"

python3 -m benchexec.benchexec "comparison_$1.xml" --numOfThreads $2 --outputpath "$RESULT_DIR"

./plot.sh $RESULT_DIR
