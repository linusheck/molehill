#!/bin/sh
rm -rf results
python3 -m benchexec.benchexec comparison.xml --numOfThreads 16
table-generator results/*xml.bz2   --all-columns
