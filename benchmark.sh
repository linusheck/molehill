#!/bin/sh
# Call this script with argument "simple" or "robust" 


# RESULT_DIR="results/$1-$(date +"%Y-%m-%d_%H-%M-%S")"
# mkdir -p "$RESULT_DIR"

# python3 -m benchexec.benchexec "comparison_$1.xml" --numOfThreads $2 --outputpath "$RESULT_DIR"

RESULT_DIR="stored_results/simple-2025-05-06_14-15-28/"

PYTHONPATH=$(pwd) python3 $(which table-generator) $(find $RESULT_DIR -type f | grep ".*results\.[^.]*\.xml\.bz2$") --all-columns -x benchmarks/tablegenerator.xml -o $RESULT_DIR

for x in $(find $RESULT_DIR -type f | grep ".*results\.[^.]*\.xml\.bz2$"); do
    echo "Processing $x"
    PYTHONPATH=$(pwd) python3 misc/plots/quantile-generator.py --correct-only $x > $RESULT_DIR/$(basename $x).quantile.csv
done

cd $RESULT_DIR

QUANTILE_NAMES=""
for file in *.quantile.csv; do
    base_name=$(basename "$file" | sed 's/.*results\.\(.*\)\.xml\.bz2\.quantile\.csv/\1/')
    QUANTILE_NAMES="$QUANTILE_NAMES$base_name,"
done

QUANTILE_FILES=$(ls *.quantile.csv | tr '\n' ', ' | sed 's/,$//')

echo "QUANTILE_NAMES: $QUANTILE_NAMES"
echo "QUANTILE_FILES: $QUANTILE_FILES"
sed -e "s|FILES|$QUANTILE_FILES|" -e "s|NAMES|$QUANTILE_NAMES|" ../../misc/plots/quantile.tex > quantile_processed.tex

for file in *.quantile.csv; do
    base_name=$(basename "$file" | sed 's/.*results\.\(.*\)\.xml\.bz2\.quantile\.csv/\1/')
    if [ "$base_name" != "Molehill" ]; then
        echo "Comparing Molehill with $base_name"
        # Get both file names (...xml.bz2)
        # and the corresponding quantile files
        # (Molehill.quantile.csv and $base_name.quantile.csv)
        molehill_file=$(ls *Molehill* | grep ".*results\.[^.]*\.xml\.bz2$")
        base_file=$(ls *$base_name* | grep ".*results\.[^.]*\.xml\.bz2$")
        echo "Molehill file: $molehill_file"
        echo "Base file: $base_file"
        sed -e "s|FILE1|$molehill_file|" -e "s|FILE2|$base_file|" ../../misc/plots/scatter.xml > scatter_$base_name.xml
        PYTHONPATH=$(pwd) python3 $(which table-generator)  -f csv -x scatter_$base_name.xml
        # Replace incorrect results with "no result" value in plot
        python ../../misc/plots/no_result.py scatter_$base_name.table.csv
        sed -e "s|SCATTER_FILE|scatter_$base_name.table.csv|" \
            -e "s|TOOL1|Molehill|" \
            -e "s|TOOL2|$base_name|" ../../misc/plots/scatter.tex > scatter_$base_name.tex
        pdflatex scatter_$base_name.tex
    fi
done

# pdflatex quantile_processed.tex

# PYTHONPATH=$(pwd) python3 misc/plots/quantile-generator.py --correct-only $(ls $RESULT_DIR/* | grep ".*results.[^.]*\.xml.bz2") > example-tool1.quantile.csv
