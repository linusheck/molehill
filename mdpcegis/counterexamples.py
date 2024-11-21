"""Compute counterexamples."""

from stormpy import model_checking, parse_properties_without_context
import stormpy.storage
import stormpy.core

def compute_counterexample(sub_mdp, mc_result, variables, partial_model, state_to_holes, prop, global_bounds):
    # pathlib.Path(f"dots/mdp_{partial_model}.dot").write_text(sub_mdp.model.to_dot(), encoding="utf-8")
    # print(sub_mdp.model.nr_states)
    size = sub_mdp.model.nr_states

    included_states = []
    not_included_states = []

    included_holes = [hole for hole in range(len(variables)) if variables[hole] not in partial_model]
    included_fixed_holes = []

    for state in range(size):
        # if the state has no holes, put it in the included states
        if len(state_to_holes[sub_mdp.quotient_state_map[state]]) == 0:
            included_states.append(state)
            continue
        # if the state's holes are all included, add it
        if all([hole in included_holes for hole in state_to_holes[sub_mdp.quotient_state_map[state]]]):
            included_states.append(state)
            continue
        # otherwise put it in the not included states
        not_included_states.append(state)

    all_schedulers_violate = False

    target_state = model_checking(sub_mdp.model, prop.formula.subformula.subformula).get_truth_values()
    one_states = [state for state in range(sub_mdp.model.nr_states) if target_state.get(state)]
    # phi_states = stormpy.storage.BitVector(sub_mdp.model.nr_states, True)
    # prob0max, _ = compute_prob01max_states(sub_mdp.model, phi_states, target_state)
    # zero_states = [state for state in range(sub_mdp.model.nr_states) if prob0max.get(state)]

    # zero_state = zero_states[-1]
    # if len(one_states) == 0:
    #     one_state = zero_state
    # else:

    while not all_schedulers_violate:
        transition_matrix = sub_mdp.model.transition_matrix

        builder = stormpy.storage.SparseMatrixBuilder(has_custom_row_grouping=True)

        zero_state = sub_mdp.model.nr_states
        one_state = sub_mdp.model.nr_states + 1

        new_row_counter = 0
        for state in range(size):
            row_group_start = transition_matrix.get_row_group_start(state)
            row_group_end = transition_matrix.get_row_group_end(state)
            builder.new_row_group(new_row_counter)
            if not state in included_states:
                builder.add_next_value(new_row_counter, zero_state, 1 - global_bounds.at(state))
                builder.add_next_value(new_row_counter, one_state, global_bounds.at(state))
                new_row_counter += 1
            else:
                for row in range(row_group_start, row_group_end):
                    for entry in transition_matrix.get_row(row):
                        builder.add_next_value(new_row_counter, entry.column, entry.value())
                    new_row_counter += 1
        builder.new_row_group(new_row_counter)
        builder.add_next_value(new_row_counter, zero_state, 1)
        builder.new_row_group(new_row_counter + 1)
        builder.add_next_value(new_row_counter + 1, one_state, 1)
        
        new_matrix = builder.build()
        # print(new_matrix)

        model_components = stormpy.storage.SparseModelComponents()
        model_components.transition_matrix = new_matrix

        state_labeling = stormpy.storage.StateLabeling(sub_mdp.model.nr_states + 2)
        state_labeling.add_label("counterexample_target")
        for state in range(sub_mdp.model.nr_states):
            for label in sub_mdp.model.labeling.get_labels_of_state(state):
                if not state_labeling.contains_label(label):
                    state_labeling.add_label(label)
                state_labeling.add_label_to_state(label, state)
            if state in one_states:
                state_labeling.add_label_to_state("counterexample_target", state)
        state_labeling.add_label_to_state("counterexample_target", one_state)

        model_components.state_labeling = state_labeling
        
        # TODO hack (i hate properties)
        new_property = parse_properties_without_context(str(prop).split()[0] + f" [ F \"counterexample_target\" ]")[0]
        new_property2 = parse_properties_without_context(str(prop.formula).split()[0] + f" [ F \"counterexample_target\" ]")[0]

        # model check filtered matrix
        new_mdp = stormpy.storage.SparseMdp(model_components)

        result2 = model_checking(new_mdp, new_property2)
        # print(included_holes, "result2", result2.at(sub_mdp.model.initial_states[0]))

        result = model_checking(new_mdp, new_property)
        all_schedulers_violate = not result.at(sub_mdp.model.initial_states[0])
        # print("all schedulers violated", all_schedulers_violate)

        # pathlib.Path(f"dots/counterexample_{partial_model}_{len(included_holes)}.dot").write_text(new_mdp.to_dot(), encoding="utf-8")

        if len(included_holes) == len(variables):
            break

        if not all_schedulers_violate:
            # choose a hole to include now
            hole_scores = [-1 if hole in included_holes else 0 for hole in range(len(variables))]
            for state in not_included_states:
                for hole in state_to_holes[sub_mdp.quotient_state_map[state]]:
                    if not hole in included_holes:
                        hole_scores[hole] += mc_result.at(state)
            # add the next state to the included states
            # argmax the mc_result over not_included_states
            # print("hole scores", hole_scores)
            max_hole = max(range(len(hole_scores)), key=lambda hole: hole_scores[hole])
            included_holes.append(max_hole)
            included_fixed_holes.append(max_hole)
            for state in not_included_states.copy():
                if all([hole in included_holes for hole in state_to_holes[sub_mdp.quotient_state_map[state]]]):
                    included_states.append(state)
                    not_included_states.remove(state)
            # print("included holes now", included_holes, "because hole scores", hole_scores)
        else:
            # print("Counterexample!!", [variables[x] for x in included_holes])
            return included_fixed_holes
    return None

