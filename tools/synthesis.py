from benchexec.tools.template import BaseTool
import sys

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

