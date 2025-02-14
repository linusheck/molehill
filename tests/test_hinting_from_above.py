""" import pytest
import stormpy
from pycarl.gmp import Rational
from time import perf_counter_ns
import csv
from fastmole import hint_convert

def parse_results(file_path):
    with open(file_path, "r", encoding="utf-8") as f:
        reader = csv.reader(f)
        first_row = reader.__next__()
        results = [float(element) for element in first_row]
    return results

results_max = parse_results("resources/test/hinting/results_max.csv")
results_min = parse_results("resources/test/hinting/results_min.csv")
print(results_max)

def is_approx(list_a, list_b, tol=1e-6, relative_tol=0):
    approx_list = [abs(a - b) < (tol + relative_tol * abs(max(a,b))) for a, b in zip(list_a, list_b)]
    if not all(approx_list):
        print(len(list_a), len(list_b))
        pos = approx_list.index(False)
        print(f"First index where list_a is not approximately equal to list_b: {pos}")
        print(f"list_a[{pos}] = {list_a[pos]}")
        print(f"list_b[{pos}] = {list_b[pos]}")
    return all(approx_list)

@pytest.mark.parametrize("vi_method", ["value_iteration"])# "optimistic_value_iteration", "value_iteration"])
@pytest.mark.parametrize("precision", [1e-6])#, 1e-6, 1e-10])
# @pytest.mark.parametrize("formula_and_results", [("Rmax=? [F \"goal\"]", results_max), ("Rmin=? [F \"goal\"]", results_min)])
@pytest.mark.parametrize("formula_and_results", [("Rmin=? [F \"goal\"]", results_min)])
def test_hinting_from_above(vi_method, precision, formula_and_results):
    # load prism file resources/test/hinting/test_hinting.prism into stormpy
    prism_program = stormpy.parse_prism_program("resources/test/hinting/test_hinting.pm")
    model = stormpy.build_sparse_model(prism_program)
    # load properties from prism file
    properties = stormpy.parse_properties(formula_and_results[0], prism_program)
    # create a model checker
    exact_environment = stormpy.core.Environment()
    exact_environment.solver_environment.minmax_solver_environment.precision = Rational(
        precision
    )
    exact_environment.solver_environment.minmax_solver_environment.method = stormpy.MinMaxMethod.__dict__[vi_method]

    # get a scheduler
    # result_sched = stormpy.check_model_sparse(model, properties[0], environment=exact_environment, extract_scheduler=True)

    # assert len(result_sched.get_values()) == len(formula_and_results[1])

    # sched = result_sched.scheduler

    def check_with_hint(hint):
        # hint_obj = stormpy.ExplicitModelCheckerHintDouble()
        # hint_obj.set_result_hint(hint[0])
        # hint_obj.set_scheduler_hint(hint[1])
        hint_obj = hint_convert(hint[0], stormpy.storage.BitVector(len(hint), True), stormpy.storage.BitVector(len(hint), True))
        print(hint_obj)
        print("Setting result hint to", hint[0])
        time = perf_counter_ns()
        result = stormpy.check_model_sparse(model, properties[0], environment=exact_environment, hint=hint_obj)
        elapsed_time = perf_counter_ns() - time
        # print(formula_and_results[0], result.get_values())
        # print(precision)
        if vi_method != "value_iteration":
            assert is_approx(result.get_values(), formula_and_results[1], tol=precision, relative_tol=precision)
        return elapsed_time

    hints = [
        # (None, None),
        # hint from below
        # ([x - 0.01 for x in formula_and_results[1]], None),
        # # hint from above
        # ([x - 0.01 for x in formula_and_results[1]], None),
        # # hint with exact results
        # (formula_and_results[1], None),
        # # hint from below with scheduler
        ([x for x in formula_and_results[1]], None),
        # # hint with exact results and scheduler
        # (formula_and_results[1], None),
    ]
    elapsed_times = [check_with_hint(hint) for hint in hints]
    print(elapsed_times)
    assert False
 """