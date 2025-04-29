for i in sat_dpm sat_grid sat_grid-10-sl-4fsc sat_grid-meet-sl-2fsc sat_herman sat_maze sat_maze-sl-5 sat_pole sat_pole-res sat_refuel-06-res ; do
    python create_benchmark.py simple ../../../resources/benchmark/jair/$i ../../sat.txt true
done

for i in sat_network sat_network-priorities sat_samplerocks dontknow_hallway dontknow_crypt dontknow_drone dontknow_network-priorities ; do
    python create_benchmark.py simple ../../../resources/benchmark/pomdps/$i ../../sat.txt true
done

for i in unsat_dpm unsat_grid unsat_grid-10-sl-4fsc unsat_grid-meet-sl-2fsc unsat_herman unsat_maze unsat_maze-sl-5 unsat_pole unsat_pole-res unsat_refuel-06-res ; do
    python create_benchmark.py simple ../../../resources/benchmark/jair/$i ../../unsat.txt false
done

for i in unsat_network unsat_samplerocks ; do
    python create_benchmark.py simple ../../../resources/benchmark/pomdps/$i ../../unsat.txt false
done

for i in avoid-8-2 avoid-8-2-easy dpm-switch-q10 dpm-switch-q10-big obstacles-10-6-skip-easy obstacles-demo rocks-6-4 rover-100-big rover-1000 uav-operator-roz-workload uav-roz ; do
    python create_benchmark.py robust ../../../resources/mdp-sketches/atva-sat/$i ../../sat.txt true
done

for i in bridge-11-5-4 bridge-21-7-9 bridge-5-3-1 masterextra-2-4-3 mastermind-2-4-3 pacman-6 rocks-3-2 rocks-4-1 rocks-4-2 rocks-8-1; do
    python create_benchmark.py robust ../../../resources/mdp-sketches/atva-sat/$i ../../sat.txt true
done
