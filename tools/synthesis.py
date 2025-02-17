from benchexec.tools.template import BaseTool
import sys
import re

class Tool(BaseTool):
    def executable(self):
        # Specify the path to the Python executable or any executable
        return sys.executable

    def name(self):
        # Return the name of your tool
        return "synthesis"

    def cmdline(self, executable, options, tasks, propertyfile=None, rlimits={}):
        # Build the command line
        return [executable] + options + tasks

    def get_value_from_output(self, lines, identifier):
        print("get value from output")
        """
        Extracts a statistic based on the identifier.
        """
        print(lines, identifier)
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
        if found_line:
            return str(iterations)
        return None
