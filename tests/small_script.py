import fastmole
import stormpy
import stormpy.examples
import stormpy.examples.files
import time
from pycarl.gmp import Rational

path = stormpy.examples.files.prism_mdp_coin_2_2
prism_program = stormpy.parse_prism_program(path)
formula_str = 'Rmin=? [F "finished"]'
properties = stormpy.parse_properties_for_prism_program(formula_str, prism_program)

environment = stormpy.core.Environment()
environment.solver_environment.minmax_solver_environment.precision = Rational(
    1e-6
)
environment.solver_environment.minmax_solver_environment.method = stormpy.MinMaxMethod.interval_iteration

model = stormpy.build_model(prism_program)

time0 = time.time()
for i in range(1000):
    result = stormpy.check_model_sparse(model, properties[0], environment=environment)
time0 = time.time() - time0

# make a hint
hint = stormpy.ExplicitModelCheckerHintDouble()
hint.set_result_hint([x + 0.2 for x in result.get_values()])

hint = fastmole.set_end_components_true(hint)

time1 = time.time()
for i in range(1000):
    result2 = stormpy.check_model_sparse(model, properties[0], hint=hint, environment=environment)
time1 = time.time() - time1

print(time0, time1)