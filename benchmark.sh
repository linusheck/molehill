#!/bin/sh
# Call this script with argument "simple" or "robust" 


# RESULT_DIR="results/$1-$(date +"%Y-%m-%d_%H-%M-%S")"
# mkdir -p "$RESULT_DIR"

# python3 -m benchexec.benchexec "comparison_$1.xml" --numOfThreads $2 --outputpath "$RESULT_DIR"

RESULT_DIR="results_current"

PYTHONPATH=$(pwd) python3 $(which table-generator) $(find $RESULT_DIR -type f | grep ".*results\.[^.]*\.xml\.bz2$") --all-columns -x benchmarks/tablegenerator.xml -o $RESULT_DIR

for x in $(find $RESULT_DIR -type f | grep ".*results\.[^.]*\.xml\.bz2$"); do
    echo "Processing $x"
    PYTHONPATH=$(pwd) python3 misc/plots/quantile-generator.py --correct-only $x > $RESULT_DIR/$(basename $x).quantile.csv
done

cd $RESULT_DIR
QUANTILE_NAMES=""
for file in *.quantile.csv; do
    base_name=$(basename "$file" | sed 's/.*results\.\(.*\)\.xml\.bz2\.quantile\.csv/\1/')
    QUANTILE_NAMES="$QUANTILE_NAMES, $base_name"
done

QUANTILE_FILES=$(ls *.quantile.csv | tr '\n' ', ' | sed 's/,$//')

sed -e "s|FILES|$QUANTILE_FILES|" -e "s|NAMES|$QUANTILE_NAMES|" ../misc/plots/quantile.tex > quantile_processed.tex

pdflatex quantile_processed.tex


# PYTHONPATH=$(pwd) python3 misc/plots/quantile-generator.py --correct-only $(ls $RESULT_DIR/* | grep ".*results.[^.]*\.xml.bz2") > example-tool1.quantile.csv
