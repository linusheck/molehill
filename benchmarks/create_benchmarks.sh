#!/bin/bash

rm -rf files/*

# Q1 Benchmarks

# find all sat benchmarks without memory
for i in $(find ../resources/benchmark-q1 -type d -name 'sat_*' ! -name 'sat_mem_*'); do
    python create_benchmark.py simple-q1 ../../$i ../../sat.txt true
done

# find all unsat benchmarks without memory
for i in $(find ../resources/benchmark-q1 -type d -name 'unsat_*' ! -name 'unsat_mem_*'); do
    python create_benchmark.py simple-q1 ../../$i ../../unsat.txt false
done

for mem in 1 2 3 4; do
    for i in $(find ../resources/benchmark-q1 -type d -name "sat_mem_$mem*"); do
        python create_benchmark.py simple-q1 ../../$i ../../sat.txt true --memory $mem
    done
    for i in $(find ../resources/benchmark-q1 -type d -name "unsat_mem_$mem*"); do
        python create_benchmark.py simple-q1 ../../$i ../../unsat.txt false --memory $mem
    done
done



# Q2 Benchmarks: Cost Benchmarks
for i in $(find ../resources/benchmark-q2-cost -type d -name 'sat_*'); do
    python create_benchmark.py benchmark-q2-cost ../../$i ../../sat.txt true
done
for i in $(find ../resources/benchmark-q2-cost -type d -name 'unsat_*'); do
    python create_benchmark.py benchmark-q2-cost ../../$i ../../unsat.txt false
done

# Q2 Benchmarks: Tree Benchmarks
for i in $(find ../resources/benchmark-q2-tree -type d -name 'sat_*'); do
    python create_benchmark.py benchmark-q2-tree ../../$i ../../sat.txt true
done
for i in $(find ../resources/benchmark-q2-tree -type d -name 'unsat_*'); do
    python create_benchmark.py benchmark-q2-tree ../../$i ../../unsat.txt false
done

# Q2 Benchmarks: Prob>0 Benchmarks

# find all sat benchmarks without memory
for i in $(find ../resources/benchmark-q2-prob0 -type d -name 'sat_*' ! -name 'sat_mem_*'); do
    python create_benchmark.py benchmark-q2-prob0 ../../$i ../../sat.txt true
done
# find all unsat benchmarks without memory
for i in $(find ../resources/benchmark-q2-prob0 -type d -name 'unsat_*' ! -name 'unsat_mem_*'); do
    python create_benchmark.py benchmark-q2-prob0 ../../$i ../../unsat.txt false
done
for mem in 1 2 3 4; do
    for i in $(find ../resources/benchmark-q2-prob0 -type d -name "sat_mem_$mem*"); do
        python create_benchmark.py benchmark-q2-prob0 ../../$i ../../sat.txt true --memory $mem
    done
    for i in $(find ../resources/benchmark-q2-prob0 -type d -name "unsat_mem_$mem*"); do
        python create_benchmark.py benchmark-q2-prob0 ../../$i ../../unsat.txt false --memory $mem
    done
done

# Q3 Benchmarks

# find all sat benchmarks without memory
for i in $(find ../resources/benchmark-q3 -type d -name 'sat_*' ! -name 'sat_mem_*'); do
    python create_benchmark.py robust-q3 ../../$i ../../sat.txt true
done

# find all unsat benchmarks without memory
for i in $(find ../resources/benchmark-q3 -type d -name 'unsat_*' ! -name 'unsat_mem_*'); do
    python create_benchmark.py robust-q3 ../../$i ../../unsat.txt false
done

for mem in 1 2 3; do
    for i in $(find ../resources/benchmark-q3 -type d -name "sat_mem_$mem*"); do
        python create_benchmark.py robust-q3 ../../$i ../../sat.txt true --memory $mem
    done
    for i in $(find ../resources/benchmark-q3 -type d -name "unsat_mem_$mem*"); do
        python create_benchmark.py robust-q3 ../../$i ../../unsat.txt false --memory $mem
    done
done


for nodes in 1 3 5 7 9 11 13 15; do
    for i in $(find ../resources/benchmark-general -type d -name 'sat_*'); do
        python create_benchmark.py benchmark-general ../../$i ../../unknown.txt unknown --nodes $nodes
    done
done
