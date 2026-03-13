#!/bin/sh

RESULT_DIR=$1

PYTHONPATH=$(pwd) python3 $(which table-generator) $(find $RESULT_DIR -type f | grep ".*results\..*\.xml\.bz2$") --all-columns -x benchmarks/tablegenerator.xml -o $RESULT_DIR