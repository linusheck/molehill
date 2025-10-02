# <img src="resources/molehill.svg" alt="Molehill Logo" height="25"/> Molehill Markov chain searcher 

## Installation

### (a) For users

To build **molehill** from source run (NOTE THIS WILL WORK ONLY AFTER WE RELEASE PAYNT ON PYPI): 
```
git clone https://github.com/linusheck/molehill.git
cd molehill
python3 -m venv venv && source venv/bin/activate
pip install .
```

### (b) For developers

**molehill** depends on [Storm](https://github.com/moves-rwth/storm), [stormpy](https://github.com/moves-rwth/stormpy) and [paynt](https://github.com/randriu/synthesis). For developers, we recommend having local installations of all Storm,stormpy and paynt (see [section below](#installing-dependencies)). If you have stormpy and paynt already installed in your developer environment, you can use:

```shell
pip install -r build-requirements.txt
pip install . --no-build-isolation
```

which builds and installs molehill directly into your environment. **Note that the Storm backends used by molehill, paynt and stormpy need to be the same.**

#### installing-dependencies

Please refer to [Storm documentation](https://www.stormchecker.org/documentation/obtain-storm/build.html), [stormpy documentation](https://moves-rwth.github.io/stormpy/installation.html) and [paynt README](https://github.com/randriu/synthesis/blob/master/README.md) for more information. Here we provide a list of commands that build master branch of Storm, stormpy and paynt in virtual environment without further explanation:

```shell
python3 -m venv venv && source venv/bin/activate
mkdir prerequisites && cd prerequisites
git clone https://github.com/moves-rwth/storm.git
git clone https://github.com/moves-rwth/stormpy.git
git clone https://github.com/randriu/synthesis.git
mkdir storm/build && cd storm/build
cmake ..
make storm storm-cli storm-pomdp
cd - && cd stormpy
pip install . --config-settings=cmake.define.USE_STORM_DFT=OFF --config-settings=cmake.define.USE_STORM_GSPN=OFF
cd - && cd synthesis
pip install . --no-build-isolation
```

## Run molehill

For help, execute
```
python -m molehill --help
```

### Benchmarking

Only seems to work on Linux. You need to install BenchExec:
```
pip install BenchExec
```

Then execute:
```
./benchmark.sh
```

## Writing your own constraints

Because molehill is based on a simple Z3 call, you can impose arbitary constraints on the search space. This can be done as follows:

1.  Create a class that extends `molehill/constraints/constraint.py`. Implement the API:
```
class Constraint:
    """Base class for constraints."""

    def __init__(self):
        self.args = None

    def solver_settings(self, solver: z3.Solver) -> None:
        """Set custom solver settings here."""

    def register_arguments(self, argument_parser: argparse.ArgumentParser) -> None:
        """Register arguments for the constraint."""

    def set_args(self, args: argparse.Namespace) -> None:
        """Set the arguments for the constraint."""
        self.args = args
    
    def optimize(self) -> z3.ExprRef:
        """Optimize something?"""
        return None

    def build_constraint(
        self,
        function: z3.Function,
        variables: list[z3.Var],
        variables_in_ranges: Callable[[list[z3.Var]], z3.ExprRef],
        **args,
    ) -> z3.ExprRef:
        """Implement your constraint here. Arguments are passed by args. Call
        variables_in_ranges on variables to get a Z3 expression that represents
        that the variables are in-range."""
        raise NotImplementedError("Constraint does not implement build_constraint")

    def show_result(self, model: z3.Model, solver: z3.Solver, **args) -> None:
        """Called after SAT. Print and/or show your result here."""
```
2. Place the file as `constraint.py` in your project.
3. Call molehill with `--constraint custom`.
