from benchexec.tools.template import BaseTool

class Tool(BaseTool):
    def executable(self):
        # Specify the path to the Python executable or any executable
        return "/home/lheck/.local/share/virtualenvs/mdpcegis-hF3SegUM/bin/python"

    def version(self, executable):
        # Return the version of the tool (optional)
        return "unknown"

    def name(self):
        # Return the name of your tool
        return "synthesis"

    def cmdline(self, executable, options, tasks, propertyfile=None, rlimits={}):
        # Build the command line
        return [executable] + options + tasks

