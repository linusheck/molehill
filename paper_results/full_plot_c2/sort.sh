#!/bin/bash

# Check if an input file was provided
if [ "$#" -ne 1 ]; then
    echo "Usage: $0 <input_file.tsv>"
    exit 1
fi

input_file="$1"
output_file="sorted.tsv"

# Sort by 6th column (CPU time), then re-index the first column
sort -k6,6n "$input_file" | \
awk -F'\t' 'BEGIN {OFS=FS} { $1=NR-1; print }' > "$output_file"

echo "Sorted and re-indexed output written to $output_file"
