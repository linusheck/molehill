from benchexec.tools.template import BaseTool2
import benchexec.result as result
import sys
import re


class Tool(BaseTool2):
    def executable(self, tool_locator):
        return sys.executable

    def name(self):
        return "causality-collect"

    def cmdline(self, executable, options, task, rlimits):
        if task.options is not None and "threshold" in task.options:
            options += ["--threshold", str(task.options["threshold"])]
        if task.options is not None and "time_limit" in task.options:
            options += ["--time-limit", str(task.options["time_limit"])]
        return [executable, *options, *task.input_files_or_identifier]

    def get_value_from_output(self, lines, identifier):
        """
        Extracts a value from the CAUSALITY_RESULT line.
        identifier is one of: threshold, smallest_tree_nodes, conflicts_processed,
                               elapsed_seconds, timed_out, tree_size_dist,
                               cause_size_dist
        """
        for line in reversed(lines):
            if line.startswith("CAUSALITY_RESULT"):
                match = re.search(rf"{identifier}=(\S+)", line)
                if match:
                    return match.group(1)
        return None

    def determine_result(self, run):
        if run.exit_code.signal is None:
            for line in reversed(run.output):
                if line.startswith("CAUSALITY_RESULT"):
                    return "done"
            return result.RESULT_UNKNOWN
        elif run.termination_reason == "cputime":
            return result.RESULT_TIMEOUT
        elif run.termination_reason == "memout":
            return "MEMOUT"
        return result.RESULT_UNKNOWN
