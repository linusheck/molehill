from benchexec.tools.template import BaseTool2
import benchexec.result as result
import sys
import re

class Tool(BaseTool2):
    def executable(self, tool_locator):
        # Specify the path to the Python executable or any executable
        return sys.executable

    def name(self):
        # Return the name of your tool
        return "synthesis"

    def get_value_from_output(self, lines, identifier):
        """
        Extracts a statistic based on the identifier.
        """
        if identifier == "iterations":
            return self._extract_iterations(lines)
        return None

    def _extract_iterations(self, output):
        iterations = 0
        found_line = False
        for line in output:
            # molehill output
            match = re.search(r"^Considered (\d+) models$", line)
            if match:
                # molehill only has one "iterations line"
                found_line = True
                iterations = int(match.group(1))
                break
            # paynt output
            match = re.search(r"^.*, iterations: (\d+)$", line)
            if match:
                # PAYNT may have MDP and DTMC iterations printed separately
                iterations += int(match.group(1))
                found_line = True
        if found_line:
            return str(iterations)
        return None
    
    def determine_result(self, run):
        if run.exit_code.signal is None:
            last_10_lines = run.output[-10:-1]
            if "sat" in last_10_lines:
                return "true"
            elif "unsat" in last_10_lines:
                return "false"
            elif "feasible: yes" in last_10_lines:
                return "true"
            elif "feasible: no" in last_10_lines:
                return "false"
            return result.RESULT_UNKNOWN
        elif run.termination_reason == "cputime":
            return result.RESULT_TIMEOUT
        elif run.termination_reason == "memout":
            return "MEMOUT"
        return result.RESULT_UNKNOWN

