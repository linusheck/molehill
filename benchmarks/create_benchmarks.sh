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



for i in $(find ../resources/benchmark-general -type d -name 'sat_*'); do
    python create_benchmark.py benchmark-general ../../$i ../../sat.txt true
done
for i in $(find ../resources/benchmark-general -type d -name 'unsat_*'); do
    python create_benchmark.py benchmark-general ../../$i ../../unsat.txt false
done


# Old Robust Benchmarks
# for i in avoid-8-2 avoid-8-2-easy dpm-switch-q10 dpm-switch-q10-big obstacles-10-6-skip-easy obstacles-demo rocks-6-4 rover-100-big rover-1000 uav-operator-roz-workload uav-roz ; do
#     python create_benchmark.py robust ../../../resources/mdp-sketches/atva-sat/$i ../../sat.txt true
# done

# for i in bridge-11-5-4 bridge-21-7-9 bridge-5-3-1 mastermind-2-4-3 pacman-6 rocks-3-2 rocks-4-1 rocks-4-2 rocks-8-1; do
#     python create_benchmark.py robust ../../../resources/mdp-sketches/other/$i ../../sat.txt true
# done

# for i in exponential-8 exponential-20; do
#     python create_benchmark.py robust ../../../resources/mdp-sketches/other/$i ../../unsat.txt false
# done
