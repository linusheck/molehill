"""Compute counterexamples."""

from stormpy import check_model_sparse, model_checking, parse_properties_without_context, get_reachable_states
import stormpy.storage
import stormpy.core
import z3
# import pathlib

def compute_counterexample(sub_mdp, mc_result, variables, partial_model, state_to_holes, choice_to_assignment, prop, matrix_generator, model_counter):
    print("Compute counterexample")
    # pathlib.Path(f"dots/mdp_{partial_model}.dot").write_text(sub_mdp.model.to_dot(), encoding="utf-8")
    transition_matrix = sub_mdp.model.transition_matrix

    included_holes = [hole for hole in range(len(variables)) if variables[hole] not in partial_model]
    included_choices = set([choice for choice in range(len(choice_to_assignment)) if all([hole in included_holes for hole, _ in choice_to_assignment[choice]])])
    included_fixed_holes = []

    # compute hole_scores
    hole_scores = [0.0] * len(variables)
    for state, quotient_state in enumerate(sub_mdp.quotient_state_map):
        for hole in state_to_holes[quotient_state]:
            if not hole in included_holes:
                for successor in transition_matrix.get_row(state):
                    if successor.value() > 0:
                        hole_scores[hole] += mc_result.at(successor.column)
    # print(hole_scores)
    if not any([score > 0.0 for score in hole_scores]):
        return None

    all_schedulers_violate = False

    target_state = model_checking(sub_mdp.model, prop.formula.subformula.subformula).get_truth_values()
    one_states = [state for state in range(sub_mdp.model.nr_states) if target_state.get(state)]

    hint = None

    model_components = stormpy.storage.SparseModelComponents()
    state_labeling = matrix_generator.build_state_labeling(sub_mdp, one_states)
    model_components.state_labeling = state_labeling

    while not all_schedulers_violate:
        included_choices = set([choice for choice in range(len(choice_to_assignment)) if all([hole in included_holes for hole, _ in choice_to_assignment[choice]])])
        submatrix = matrix_generator.build_matrix(sub_mdp, included_choices)

        model_components.transition_matrix = submatrix

        # TODO hack (i hate properties)
        new_property = parse_properties_without_context(str(prop.formula).split()[0] + " [ F \"counterexample_target\" ]")[0]

        # model check filtered matrix
        new_mdp = stormpy.storage.SparseMdp(model_components)

        result = check_model_sparse(new_mdp, new_property, extract_scheduler=True, hint=hint)
        # for state in range(sub_mdp.model.nr_states):
        #     # also #print variable valuations
        #     print(sub_mdp.quotient_choice_map[state], result.at(state))
        # print(result.get_values()[new_mdp.initial_states[0]], prop)
        # hint = ExplicitModelCheckerHintDouble()
        # hint.set_result_hint(result.get_values())
        # hint.set_scheduler_hint(result.scheduler)
        all_schedulers_violate = not prop.satisfies_threshold(result.at(new_mdp.initial_states[0]))

        # print("Write to", f"dots/counterexample_{partial_model}_{len(included_holes)}.dot")
        # pathlib.Path(f"dots/counterexample_{partial_model}_{len(included_holes)}.dot").write_text(new_mdp.to_dot(), encoding="utf-8")

        if not all_schedulers_violate:
            condition_before_candidate = z3.And(*[variables[hole] == partial_model[variables[hole]] for hole in included_fixed_holes])
            assignment_candidates = [None if (hole in included_holes or hole_scores[hole] == 0) else variables[hole] == partial_model[variables[hole]] for hole in range(len(variables))]

            model_counts = []
            for candidate in assignment_candidates:
                if candidate is None:
                    model_counts.append(0)
                else:
                    model_counts.append(model_counter.count_models(max_models=64, condition=z3.And(candidate, condition_before_candidate)))

            add_new_hole = True

            score = [(int(hole_scores[hole] > 0), model_counts[hole], hole_scores[hole]) for hole in range(len(variables))]

            while add_new_hole:
                max_hole = sorted(set(range(len(variables))) - set(included_holes), key=lambda hole: score[hole])[-1]
                # print("=>", max_hole)
                if score[max_hole][2] <= 0.0:
                    return None
                included_holes.append(max_hole)
                included_fixed_holes.append(max_hole)
                hole_scores[max_hole] = 0
                if len(included_holes) == len(variables):
                    return included_fixed_holes
                # Check if we have enabled a new action
                for choice, assignment in enumerate(choice_to_assignment):
                    holes = [x[0] for x in assignment]
                    if max_hole in holes and all([hole in included_holes for hole in holes]):
                        included_choices.add(choice)
                        add_new_hole = False
                # assert included_choices == set([choice for choice in range(len(choice_to_assignment)) if all([hole in included_holes for hole, _ in choice_to_assignment[choice]])])
        else:
            return included_fixed_holes
    raise RuntimeError("No counterexample found")
