        variable_value_pairs_orig = []
        with open(os.path.join(args["project_path"], "values.csv"), "r") as f:
            header = f.readline().strip().split(",")
            for line in f:
                values = line.strip().split(",")
                variable_value_pairs_orig.append(
                    {header[i]: float(values[i]) for i in range(len(header))}
                )

        variable_value_pairs = []
        
        quotient = args["quotient"]
        choice_to_hole_options = quotient.coloring.getChoiceToAssignment()
        transition_matrix = quotient.quotient_mdp.transition_matrix
        
        # go through transition matrix 
        for state in range(quotient.quotient_mdp.nr_states):
            first_row = transition_matrix.get_rows_for_group(state)[0]
            if len(choice_to_hole_options[first_row]) == 0:
                pass
            else:
                variable_value_pairs.append(variable_value_pairs_orig[state])

        # Use filtered variable_value_pairs
        property_names = list(variable_value_pairs[0].keys())
        self.property_names = property_names
        num_properties = len(property_names)
