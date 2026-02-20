import re
import sys

def process_file(input_path, output_path):
    with open(input_path, 'r') as f:
        lines = f.readlines()

    output_lines = []
    current_state_lines = []
    
    # regex for state header: "state 123 {label} ..."
    state_pattern = re.compile(r'^state\s+(\d+)\s+.*')
    
    # Regex for action line: "    action name"
    # It seems indented by tab or spaces.
    action_pattern = re.compile(r'^\s+action\s+(\w+)')
    
    # Regex for transition: "        123 : 0.456"
    transition_pattern = re.compile(r'^\s+(\d+)\s+:\s+([0-9.]+)')

    # We also need to capture headers (lines before first state)
    headers = []
    body_started = False
    
    # Helper to process a block of lines for one state
    def process_state_block(block):
        if not block:
            return []
            
        header_line = block[0]
        # Parse actions
        # Structure: action_name -> list of (target, prob)
        # We use list of tuples and sort them to compare distributions canonically
        actions = {}
        current_action = None
        
        for line in block[1:]:
            m_act = action_pattern.match(line)
            m_trans = transition_pattern.match(line)
            
            if m_act:
                current_action = m_act.group(1)
                actions[current_action] = []
            elif m_trans and current_action:
                target = int(m_trans.group(1))
                prob = float(m_trans.group(2))
                actions[current_action].append((target, prob))
        
        # Now compare distributions
        # If no actions, return block as is
        if not actions:
            return block
            
        # Normalize distributions for comparison
        # Sort by target
        normalized_actions = []
        for act_name, trans_list in actions.items():
            # Sort by target state
            sorted_trans = sorted(trans_list, key=lambda x: x[0])
            normalized_actions.append(sorted_trans)
            
        # Check if all normalized actions are identical
        # Compare first to rest
        first = normalized_actions[0]
        all_same = True
        for other in normalized_actions[1:]:
            if other != first:
                all_same = False
                break
        
        if all_same:
            print(block)
            return [header_line, "\taction noop\n", block[2]]
        else:
            return block

    for line in lines:
        if state_pattern.match(line):
            if not body_started:
                body_started = True # Start of first state
            
            # Flush previous state
            if current_state_lines:
                processed = process_state_block(current_state_lines)
                output_lines.extend(processed)
                current_state_lines = []
            
            current_state_lines.append(line)
        else:
            if body_started:
                current_state_lines.append(line)
            else:
                output_lines.append(line)
                
    # Flush last state
    if current_state_lines:
        processed = process_state_block(current_state_lines)
        output_lines.extend(processed)

    with open(output_path, 'w') as f:
        f.writelines(output_lines)
        
if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python simplify_model_fixed.py <input> [output]")
        sys.exit(1)
    
    inp = sys.argv[1]
    out = sys.argv[2] if len(sys.argv) > 2 else inp
    process_file(inp, out)
