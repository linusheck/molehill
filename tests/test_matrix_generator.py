"""Test matrix generator"""

import pytest
from paynt.parser.sketch import Sketch
from molehill.plugin import SearchMarkovChain
from molehill.counterexamples import hole_order
import z3
import math
from stormpy import check_model_sparse, parse_properties_without_context
from stormpy.storage import BitVector
import time

def is_approx(list_a, list_b, tol=1e-6):
    approx_list = [all(abs(a - b) < tol for a, b in zip(list_a, list_b))]
    if not all(approx_list):
        print(len(list_a), len(list_b))
        pos = approx_list.index(False)
        print(f"First index where list_a is not approximately equal to list_b: {pos}")
        print(f"list_a[{pos}] = {list_a[pos]}")
        print(f"list_b[{pos}] = {list_b[pos]}")
    return all(approx_list)

def is_smaller(list_a, list_b, tol=1e-6):
    smaller_list = [a < b + tol for a, b in zip(list_a, list_b)]
    if not all(smaller_list):
        print(len(list_a), len(list_b))
        pos = smaller_list.index(False)
        print(f"First index where list_a is not smaller than list_b: {pos}")
        print(f"list_a[{pos}] = {list_a[pos]}")
        print(f"list_b[{pos}] = {list_b[pos]}")
        print(list_a[:100])
        print(list_b[:100])
    return all(smaller_list)

def pad_vector_to_size(vector, size):
    return vector + [0.0] * (size - len(vector))

@pytest.mark.parametrize("project_path", ["resources/test/grid", "resources/test/power", "resources/test/safety", "resources/test/pnueli-zuck-3"])
def test_matrix_generator(project_path):
    sketch_path = f"{project_path}/sketch.templ"
    properties_path = f"{project_path}/sketch.props"
    quotient = Sketch.load_sketch(sketch_path, properties_path)
    # print all python properties of quotient
    family = quotient.family

    s = z3.Solver()

    variables = []
    # create variables
    num_bits = max([math.ceil(math.log2(max(family.hole_options(hole)) + 1)) for hole in range(family.num_holes)]) + 1
    for hole in range(family.num_holes):
        name = family.hole_name(hole)
        options = family.hole_options(hole)
        var = z3.BitVec(name, num_bits)
        variables.append(var)
        s.add(z3.And(var >= z3.BitVecVal(min(options), num_bits), var <= z3.BitVecVal(max(options), num_bits)))

    new_family = family

    choice_to_assignment = quotient.coloring.getChoiceToAssignment()

    plugin = SearchMarkovChain(s, quotient)
    quotient_mdp = quotient.family.mdp.model

    # time to build the MDP
    fastmole_time = 0.0
    paynt_time = 0.0

    for hole in range(family.num_holes + 1):
        prop = quotient.specification.all_properties()[0]

        hole_options = [
            family.family.holeOptionsMask(hole) for hole in range(family.num_holes)
        ]
        fixed_holes = [
            hole for hole in range(family.num_holes) if len(family.hole_options(hole)) <= 1
        ]
        plugin.matrix_generator.build_submodel(BitVector(family.num_holes, False), hole_options)
        bfs_order = plugin.matrix_generator.get_current_bfs_order()
        abstracted_holes = hole_order(bfs_order, choice_to_assignment, fixed_holes)

        # Build MDP
        ex_time = time.time()
        plugin.matrix_generator.build_submodel(BitVector(family.num_holes, False), hole_options)
        fastmole_time += time.time() - ex_time
        mdp_nondet = plugin.matrix_generator.get_current_mdp()
        nondet_bitvec = plugin.matrix_generator.get_current_reachable_states()

        # Build MDP with holes
        plugin.matrix_generator.build_submodel(BitVector(family.num_holes, abstracted_holes), hole_options)
        mdp_holes = plugin.matrix_generator.get_current_mdp()
        holes_bitvec = plugin.matrix_generator.get_current_reachable_states()

        new_property = parse_properties_without_context(str(prop.formula).split()[0] + " [ F \"counterexample_target\" ]")[0]
        assert "max" in str(new_property)

        ex_time = time.time()
        quotient.build(new_family)
        paynt_time += time.time() - ex_time

        result_paynt = new_family.mdp.model_check_property(prop)
        result_storm_holes = check_model_sparse(mdp_holes, new_property)
        result_storm_nondet = check_model_sparse(mdp_nondet, new_property)

        # for the states where there is no value, we assume True by default
        result_storm_holes_pad = [max(result_storm_nondet.get_values()) + 1.0] * quotient_mdp.transition_matrix.nr_rows
        for i, state_in_holes_result in enumerate(holes_bitvec):
            result_storm_holes_pad[state_in_holes_result] = result_storm_holes.get_values()[i]

        result_storm_nondet_pad = [0.0] * quotient_mdp.transition_matrix.nr_rows
        for i, state_in_nondet_result in enumerate(nondet_bitvec):
            result_storm_nondet_pad[state_in_nondet_result] = result_storm_nondet.get_values()[i]

        assert is_smaller(result_storm_nondet_pad, result_storm_holes_pad, 1e-1)
        assert is_approx(result_paynt.result.get_values(), result_storm_nondet.get_values(), 1e-1)

        if hole < family.num_holes:
            new_family.hole_set_options(hole, [new_family.hole_options(hole)[-1]])
            new_family.add_parent_info(family)

    # assert fastmole_time < paynt_time / 2
