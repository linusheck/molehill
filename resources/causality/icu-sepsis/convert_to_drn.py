import csv

def convert_csv_to_drn(input_csv_path, output_drn_path, mdp=False):
    """
    Converts an NxN transition probability CSV into a sparse DRN file.
    """
    # Hardcoded this, sorry
    num_actions = 25

    transitions = []
    with open(input_csv_path + "/initialStateDistribution.csv", 'r') as f:
        reader = csv.reader(f)
        for row in reader:
            for i in range(num_actions):
                transitions.append([0.0] + [float(x) for x in row])
    with open(input_csv_path + "/transitionFunction.csv", 'r') as f:
        reader = csv.reader(f)
        for row in reader:
            transitions.append([0.0] + [float(x) for x in row])

    num_states = len(transitions[0])

    admissible_actions = [[0]]
    # Parse admissibleActions.txt
    with open(input_csv_path + "/extras/admissibleActions.txt", 'r') as f:
        lines = f.readlines()
        for line in lines:
            if line.strip() == "":
                continue
            numbers = [int(x) for x in line.split()]
            admissible_actions.append(numbers)
    
    assert len(admissible_actions) == num_states, f"Admissible actions length mismatch: {len(admissible_actions)} vs {num_states}"

    # rewards = []
    # with open(input_csv_path + "/rewardFunction.csv", 'r') as f:
    #     reader = csv.reader(f)
    #     for row in reader:
    #         assert rewards == [], "Expected only one row in rewardFunction.csv"
    #         rewards = [0.0] + [float(x) for x in row]
    # # Also prepend a zero to the rewards for the new init state
    # rewards.insert(0, 0.0)

    with open(output_drn_path, 'w') as f:
        # 1. Write the Header
        f.write("// Original model type: MDP\n")
        if mdp:
            f.write("@type: MDP\n")
        else:
            f.write("@type: POMDP\n")
        f.write("@nr_states\n")
        f.write(f"{num_states}\n")

        f.write("@nr_choices\n")
        f.write(str(sum(len(actions) for actions in admissible_actions)) + "\n")

        f.write("@model\n")

        # 2. Iterate through states to write transitions
        for state_idx in range(num_states):
            label = "init" if state_idx == 0 else ""

            if state_idx == num_states - 2:
                label = "survive"

            if mdp:
                f.write("state " + str(state_idx) + " " + label + "\n")
            else:
                f.write("state " + str(state_idx) + " {" + str(state_idx) + "}" + f" [0] {label}\n")

            for action in admissible_actions[state_idx]:
                f.write(f"\taction {action} [1]\n")
                row = transitions[state_idx * num_actions + action]
                has_transitions = False
                
                for target_idx, prob in enumerate(row):
                    if prob > 0.0:
                        f.write(f"\t\t{target_idx} : {prob}\n")
                        has_transitions = True
                if not has_transitions:
                    f.write(f"\t\t{state_idx} : 1.0\n")

if __name__ == "__main__":
    convert_csv_to_drn("csv-tables", "sketch.templ")
    convert_csv_to_drn("csv-tables", "mdp.drn", mdp=True)
