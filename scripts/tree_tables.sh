#!/bin/sh

RESULT_DIR=$1

PYTHONPATH=$(pwd) python3 $(which table-generator) $(find $RESULT_DIR -type f | grep ".*results\..*\.xml\.bz2$") --all-columns -x benchmarks/tablegenerator.xml -o $RESULT_DIR
PYTHONPATH=$(pwd) python3 misc/plots/unique_table.py $RESULT_DIR/tablegenerator.table.csv > $RESULT_DIR/unique_table.txt
PYTHONPATH=$(pwd) python3 misc/plots/tree_table.py $RESULT_DIR/tablegenerator.table.csv > $RESULT_DIR/tree_table.tex