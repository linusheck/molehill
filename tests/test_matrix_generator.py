"""Test matrix generator"""

import pytest
from paynt.parser.sketch import Sketch
from molehill.plugin import SearchMarkovChain
import z3
import math
from stormpy import model_checking, check_model_sparse, parse_properties_without_context
from stormpy.storage import SparseModelComponents, SparseMdp
from random import choice

def is_approx(list_a, list_b, tol=1e-6):
    return all(abs(a - b) < tol for a, b in zip(list_a, list_b))


def is_smaller(list_a, list_b, tol=1e-6):
    return all(a < b + tol for a, b in zip(list_a, list_b))

@pytest.mark.parametrize("project_path", ["resources/grid", "resources/test/grid"])
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

    quotient.build(family)

    new_family = family
    quotient.build(new_family)
    for hole in range(family.num_holes + 1):

        quotient.build(new_family)
        sub_mdp = new_family.mdp

        plugin = SearchMarkovChain(s, quotient)

        prop = quotient.specification.all_properties()[0]

        target_state = model_checking(sub_mdp.model, prop.formula.subformula.subformula).get_truth_values()
        one_states = [state for state in range(sub_mdp.model.nr_states) if target_state.get(state)]

        choice_to_assignment = quotient.coloring.getChoiceToAssignment()

        matrix_generator = plugin.matrix_generator
        
        included_holes = [hole for hole in range(len(variables)) if len(new_family.hole_options(hole)) == 1]
        included_choices = set([choice for choice in range(len(choice_to_assignment)) if all([hole in included_holes for hole, _ in choice_to_assignment[choice]])])

        print(sub_mdp.model.nr_states, sub_mdp.model.transition_matrix.nr_rows, sub_mdp.model.transition_matrix.nr_columns)
        matrix_nondet = matrix_generator.build_matrix(sub_mdp.quotient_state_map, sub_mdp.model.transition_matrix, set(range(len(choice_to_assignment))))
        matrix_holes = matrix_generator.build_matrix(sub_mdp.quotient_state_map, sub_mdp.model.transition_matrix, included_choices)
        labeling = matrix_generator.build_state_labeling(sub_mdp.model.transition_matrix, sub_mdp.model.labeling, one_states)

        model_components = SparseModelComponents()
        model_components.state_labeling = labeling

        new_property = parse_properties_without_context(str(prop.formula).split()[0] + " [ F \"counterexample_target\" ]")[0]
        model_components.transition_matrix = matrix_nondet
        mdp_nondet = SparseMdp(model_components)

        model_components.transition_matrix = matrix_holes
        mdp_holes = SparseMdp(model_components)

        result_paynt = new_family.mdp.model_check_property(prop)
        result_storm_nondet = check_model_sparse(mdp_nondet, new_property)
        result_storm_holes = check_model_sparse(mdp_holes, new_property)

        global_bounds = matrix_generator.global_bounds
        for state in range(sub_mdp.model.nr_states):
            print(global_bounds[sub_mdp.quotient_state_map[state]], sub_mdp.quotient_state_map[state], result_paynt.result.get_values()[state])
            assert global_bounds[sub_mdp.quotient_state_map[state]] >= result_paynt.result.get_values()[state]

        assert is_approx(result_paynt.result.get_values(), result_storm_nondet.get_values(), 1e-4)
        assert is_smaller(result_storm_nondet.get_values(), result_storm_holes.get_values(), 1e-4)

        if hole < family.num_holes:
            new_family = new_family.subholes(hole, [new_family.hole_options(hole)[-1]])
            new_family.add_parent_info(family)
            print(new_family)
