#!/bin/sh
rm -rf results
mkdir results
python3 -m benchexec.benchexec comparison.xml --numOfThreads 32
table-generator results/*xml.bz2   --all-columns
