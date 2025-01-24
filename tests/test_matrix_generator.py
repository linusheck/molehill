"""Test matrix generator"""

import pytest
from paynt.parser.sketch import Sketch
from molehill.plugin import SearchMarkovChain
import z3
import math
from stormpy import model_checking, check_model_sparse, parse_properties_without_context
from stormpy.storage import SparseModelComponents, SparseMdp, BitVector
from random import choice

def is_approx(list_a, list_b, tol=1e-6):
    return all(abs(a - b) < tol for a, b in zip(list_a, list_b))


def is_smaller(list_a, list_b, tol=1e-6):
    return all(a < b + tol for a, b in zip(list_a, list_b))

@pytest.mark.parametrize("project_path", ["resources/test/grid"])
# @pytest.mark.parametrize("project_path", ["resources"])
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
        # TODO hole options of full family should be a sorted vector of indices that is continous
        s.add(z3.And(var >= z3.BitVecVal(min(options), num_bits), var <= z3.BitVecVal(max(options), num_bits)))

    new_family = family

    plugin = SearchMarkovChain(s, quotient)
    print("Model transition matrix:")
    print(quotient.family.mdp.model.transition_matrix)
    for hole in range(family.num_holes + 1):
        print("new loop iteration")
        sub_mdp = new_family.mdp

        prop = quotient.specification.all_properties()[0]
        
        compatible_choices = quotient.coloring.selectCompatibleChoices(new_family.family)

        mdp_holes, holes_bitvec = plugin.matrix_generator.build_submodel(compatible_choices)
        mdp_nondet, nondet_bitvec = plugin.matrix_generator.build_submodel(BitVector(len(compatible_choices), True))

        open("mdp_holes.dot", "w").write(mdp_holes.to_dot())
        open("mdp_nondet.dot", "w").write(mdp_nondet.to_dot())

        new_property = parse_properties_without_context(str(prop.formula).split()[0] + " [ F \"counterexample_target\" ]")[0]

        # quotient.build(new_family)
        # TODO check against paynt
        # result_paynt = new_family.mdp.model_check_property(prop)
        # open("mdp_paynt.dot", "w").write(new_family.mdp.model.to_dot())
        result_storm_nondet = check_model_sparse(mdp_nondet, new_property)
        result_storm_holes = check_model_sparse(mdp_holes, new_property)

        # global_bounds = plugin.global_bounds
        # for state in range(sub_mdp.model.nr_states):
        #     print(global_bounds[sub_mdp.quotient_state_map[state]], sub_mdp.quotient_state_map[state], result_paynt.result.get_values()[state])
            # assert global_bounds[sub_mdp.quotient_state_map[state]] >= result_paynt.result.get_values()[state]
            # assert is_approx([result_paynt.result.get_values()[sub_mdp.quotient_state_map[state]]], [result_storm_nondet.get_values()[state]], 1e-4)

        # print(result_paynt.result.get_values())
        # print(result_storm_nondet.get_values())
        # assert is_approx(result_paynt.result.get_values(), result_storm_nondet.get_values(), 1e-4)
        result_storm_holes_pad = [1.0] * len(result_storm_nondet.get_values())
        for i, state_in_holes_result in enumerate(holes_bitvec):
            result_storm_holes_pad[state_in_holes_result] = result_storm_holes.get_values()[i]
        assert is_smaller(result_storm_nondet.get_values(), result_storm_holes_pad, 1e-4)

        if hole < family.num_holes:
            new_family.hole_set_options(hole, [new_family.hole_options(hole)[-1]])
            new_family.add_parent_info(family)
            print(new_family)
