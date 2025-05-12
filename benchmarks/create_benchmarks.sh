#!/bin/bash

# Simple Benchmarks

# find all sat benchmarks without memory
for i in $(find ../resources/benchmark -type d -name 'sat_*' ! -name 'sat_mem_*'); do
    python create_benchmark.py simple ../../$i ../../sat.txt true
done

# find all unsat benchmarks without memory
for i in $(find ../resources/benchmark -type d -name 'unsat_*' ! -name 'unsat_mem_*'); do
    python create_benchmark.py simple ../../$i ../../unsat.txt true
done

for mem in 1 2 3 4; do
    for i in $(find ../resources/benchmark -type d -name "sat_mem_$mem"); do
        python create_benchmark.py simple ../../$i ../../sat.txt true --memory $mem
    done
    for i in $(find ../resources/benchmark -type d -name "unsat_mem_$mem"); do
        python create_benchmark.py simple ../../$i ../../unsat.txt true --memory $mem
    done
done


# Robust Benchmarks

for i in avoid-8-2 avoid-8-2-easy dpm-switch-q10 dpm-switch-q10-big obstacles-10-6-skip-easy obstacles-demo rocks-6-4 rover-100-big rover-1000 uav-operator-roz-workload uav-roz ; do
    python create_benchmark.py robust ../../../resources/mdp-sketches/atva-sat/$i ../../sat.txt true
done

for i in bridge-11-5-4 bridge-21-7-9 bridge-5-3-1 mastermind-2-4-3 pacman-6 rocks-3-2 rocks-4-1 rocks-4-2 rocks-8-1; do
    python create_benchmark.py robust ../../../resources/mdp-sketches/other/$i ../../sat.txt true
done
