"""Compute counterexamples."""

from stormpy import check_model_sparse, model_checking, parse_properties_without_context, get_reachable_states
from stormpy.storage import BitVector
import stormpy.storage
import stormpy.core
from pycarl.gmp import Rational
import z3

def _get_possible_and_certain_choices(choice_to_assignment, abstracted_holes, family):
    selected_choices = BitVector(len(choice_to_assignment), False)
    for choice, hole_assignments in enumerate(choice_to_assignment):
        possible = True # this choice is possible (it might occur in the MDP)
        hole_abstracted = False
        for hole, assignment in hole_assignments:
            if hole in abstracted_holes:
                hole_abstracted = True
            hole_options = family.hole_options(hole)
            if assignment not in hole_options:
                possible = False
                break
        if hole_abstracted:
            # this hole is abstracted, so we can't use this choice
            selected_choices[choice] = False
        else:
            selected_choices[choice] = possible
    return selected_choices

def _check_model(mdp, prop, hint):
    exact_environment = stormpy.core.Environment()
    exact_environment.solver_environment.minmax_solver_environment.precision = Rational(1e-10)
    exact_environment.solver_environment.minmax_solver_environment.method = stormpy.MinMaxMethod.sound_value_iteration
    print("Check whether all schedulers violate")

    # TODO hack (i hate properties)
    new_prop = parse_properties_without_context(str(prop.formula).split()[0] + " [ F \"counterexample_target\" ]")[0]

    result = check_model_sparse(mdp, new_prop, extract_scheduler=True, hint=hint, environment=exact_environment)
    all_schedulers_violate = not prop.satisfies_threshold(result.at(mdp.initial_states[0]))
    print("All schedulers violate:", all_schedulers_violate)
    return all_schedulers_violate, result

def hole_order(bfs_order, choice_to_assignment):
    order = []
    for choice in bfs_order:
        for hole, _ in choice_to_assignment[choice]:
            if hole not in order:
                order.append(hole)
    return order

def check(matrix_generator, choice_to_assignment, family, prop):
    possible_choices = _get_possible_and_certain_choices(choice_to_assignment, [], family)
    matrix_generator.build_submodel(possible_choices)
    mdp = matrix_generator.get_current_mdp()
    all_schedulers_violate, result = _check_model(mdp, prop, None)
    if all_schedulers_violate:
        bfs_order = matrix_generator.get_current_bfs_order()
        # we abstract in the order of which holes we saw first, which holes we saw second, etc
        abstracted_holes = hole_order(bfs_order, choice_to_assignment)
        all_schedulers_violate = False
        while not all_schedulers_violate:
            # try to get an unsat core!!
            # let's start with abstracting all of the nondeterminism into holes
            possible_choices = _get_possible_and_certain_choices(choice_to_assignment, abstracted_holes, family)
            matrix_generator.build_submodel(possible_choices)
            mdp_holes = matrix_generator.get_current_mdp()
            all_schedulers_violate, result = _check_model(mdp_holes, prop, None)
            if all_schedulers_violate:
                # yaay we have a counterexample!!
                print("Counterexample found", abstracted_holes, family)
                return all_schedulers_violate, abstracted_holes, result
            # abstract fewer holes
            abstracted_holes = abstracted_holes[1:]
            if len(abstracted_holes) == 0:
                break
    return all_schedulers_violate, list(range(0, family.num_holes)), result

# def compute_counterexample(sub_mdp, mc_result, variables, partial_model, state_to_holes, choice_to_assignment, prop, matrix_generator, model_counter):
#     # pathlib.Path(f"dots/mdp_{partial_model}.dot").write_text(sub_mdp.model.to_dot(), encoding="utf-8")
#     transition_matrix = sub_mdp.model.transition_matrix

#     included_holes = [hole for hole in range(len(variables)) if variables[hole] not in partial_model]
#     included_choices = set([choice for choice in range(len(choice_to_assignment)) if all([hole in included_holes for hole, _ in choice_to_assignment[choice]])])
#     included_fixed_holes = []

#     # compute hole_scores
#     hole_scores = [0.0] * len(variables)
#     for state, quotient_state in enumerate(sub_mdp.quotient_state_map):
#         for hole in state_to_holes[quotient_state]:
#             if not hole in included_holes:
#                 for successor in transition_matrix.get_row(state):
#                     if successor.value() > 0:
#                         hole_scores[hole] += mc_result.at(successor.column)
#     # print(hole_scores)
#     if not any([score > 0.0 for score in hole_scores]):
#         return None

#     all_schedulers_violate = False

#     target_state = model_checking(sub_mdp.model, prop.formula.subformula.subformula).get_truth_values()
#     one_states = [state for state in range(sub_mdp.model.nr_states) if target_state.get(state)]

#     hint = None

#     model_components = stormpy.storage.SparseModelComponents()
#     state_labeling = matrix_generator.build_state_labeling(sub_mdp.model.transition_matrix, sub_mdp.model.labeling, one_states)
#     model_components.state_labeling = state_labeling

#     while not all_schedulers_violate:
#         included_choices = set([choice for choice in range(len(choice_to_assignment)) if all([hole in included_holes for hole, _ in choice_to_assignment[choice]])])
#         submatrix = matrix_generator.build_matrix(sub_mdp.quotient_state_map, sub_mdp.model.transition_matrix, included_choices)

#         model_components.transition_matrix = submatrix

#         # TODO hack (i hate properties)
#         new_property = parse_properties_without_context(str(prop.formula).split()[0] + " [ F \"counterexample_target\" ]")[0]

#         # model check filtered matrix
#         new_mdp = stormpy.storage.SparseMdp(model_components)

#         exact_environment = stormpy.core.Environment()
#         exact_environment.solver_environment.minmax_solver_environment.precision = Rational(1e-10)
#         exact_environment.solver_environment.minmax_solver_environment.method = stormpy.MinMaxMethod.sound_value_iteration
#         print("Check whether all schedulers violate")
#         result = check_model_sparse(new_mdp, new_property, extract_scheduler=True, hint=hint, environment=exact_environment)
#         # for state in range(sub_mdp.model.nr_states):
#         #     # also #print variable valuations
#         #     print(sub_mdp.quotient_choice_map[state], result.at(state))
#         # print(result.get_values()[new_mdp.initial_states[0]], prop)
#         # hint = stormpy.ExplicitModelCheckerHintDouble()
#         # hint.set_result_hint(result.get_values())
#         # hint.set_scheduler_hint(result.scheduler)
#         all_schedulers_violate = not prop.satisfies_threshold(result.at(new_mdp.initial_states[0]))
#         print("All schedulers violate:", all_schedulers_violate)

#         # print("Write to", f"dots/counterexample_{partial_model}_{len(included_holes)}.dot")
#         # pathlib.Path(f"dots/counterexample_{partial_model}_{len(included_holes)}.dot").write_text(new_mdp.to_dot(), encoding="utf-8")

#         if not all_schedulers_violate:
#             condition_before_candidate = z3.And(*[variables[hole] == partial_model[variables[hole]] for hole in included_fixed_holes])
#             assignment_candidates = [None if (hole in included_holes or hole_scores[hole] == 0) else variables[hole] == partial_model[variables[hole]] for hole in range(len(variables))]

#             model_counts = []
#             for candidate in assignment_candidates:
#                 if candidate is None:
#                     model_counts.append(0)
#                 else:
#                     model_counts.append(model_counter.count_models(max_models=64, condition=z3.And(candidate, condition_before_candidate)))

#             add_new_hole = True

#             print(new_mdp.transition_matrix.nr_rows, new_mdp.transition_matrix.nr_columns)
#             bfs_order = stormpy.bfs_sort(new_mdp)
#             print("BFS order", bfs_order)


#             score = [(int(hole_scores[hole] > 0), model_counts[hole], hole_scores[hole]) for hole in range(len(variables))]

#             while add_new_hole:
#                 max_hole = sorted(set(range(len(variables))) - set(included_holes), key=lambda hole: score[hole])[-1]
#                 # print("=>", max_hole)
#                 if score[max_hole][2] <= 0.0:
#                     return None
#                 included_holes.append(max_hole)
#                 included_fixed_holes.append(max_hole)
#                 hole_scores[max_hole] = 0
#                 if len(included_holes) == len(variables):
#                     return included_fixed_holes
#                 # Check if we have enabled a new action
#                 for choice, assignment in enumerate(choice_to_assignment):
#                     holes = [x[0] for x in assignment]
#                     if max_hole in holes and all([hole in included_holes for hole in holes]):
#                         included_choices.add(choice)
#                         add_new_hole = False
#                 # assert included_choices == set([choice for choice in range(len(choice_to_assignment)) if all([hole in included_holes for hole, _ in choice_to_assignment[choice]])])
#         else:
#             return included_fixed_holes
#     raise RuntimeError("No counterexample found")
