#include <pybind11/cast.h>
#include <pybind11/pybind11.h>
#include <pybind11/pytypes.h>
#include <pybind11/stl.h>
#include <storm/logic/Formula.h>
#include <string>
#include <vector>

#include "MatrixGenerator.h"
#include "utils.h"

#include "storm/adapters/RationalFunctionAdapter.h"
#include "storm/storage/BitVector.h"
#include "storm/storage/SparseMatrix.h"
#include "storm/utility/graph.h"

namespace py = pybind11;

PYBIND11_MODULE(fastmole, m) {
    m.doc() = R"pbdoc(
        Fastmole: molehill's fast algorithms
        -----------------------
        .. currentmodule:: fastmole
        .. autosummary::
           :toctree: _generate
    )pbdoc";

    m.def(
        "submatrix",
        [](storm::storage::SparseMatrix<double> const &matrix, storm::storage::BitVector const &rowConstraint,
           storm::storage::BitVector const &columnConstraint, bool insertDiagonalEntries = false,
           bool useGroups = true) { return matrix.getSubmatrix(useGroups, rowConstraint, columnConstraint, insertDiagonalEntries); },
        py::arg("matrix"), py::arg("row_constraint"), py::arg("column_constraint"), py::arg("insert_diagonal_entries") = false, py::arg("use_groups") = true,
        "Get submatrix");

    m.def(
        "submatrix",
        [](storm::storage::SparseMatrix<storm::RationalFunction> const &matrix, storm::storage::BitVector const &rowConstraint,
           storm::storage::BitVector const &columnConstraint, bool insertDiagonalEntries = false,
           bool useGroups = true) { return matrix.getSubmatrix(useGroups, rowConstraint, columnConstraint, insertDiagonalEntries); },
        py::arg("matrix"), py::arg("row_constraint"), py::arg("column_constraint"), py::arg("insert_diagonal_entries") = false, py::arg("use_groups") = true,
        "Get submatrix");

    // Create bindings for MatrixGenerator
    py::class_<MatrixGenerator<double>>(m, "MatrixGenerator")
        .def(py::init<const storm::models::sparse::Mdp<double> &, const storm::modelchecker::CheckTask<storm::logic::Formula, double> &,
                      const storm::storage::BitVector &, const std::vector<double> &, const std::vector<std::vector<std::pair<int, int>>> &>())
        .def("build_submodel", &MatrixGenerator<double>::buildSubModel, py::arg("abstracted_holes"), py::arg("hole_options"),
             py::arg("reachable_states") = py::none(), "Build sub model")
        .def("get_current_mdp", &MatrixGenerator<double>::getCurrentMDP, "Get current MDP")
        .def("get_current_reachable_states", &MatrixGenerator<double>::getCurrentReachableStates, "Get current reachable states")
        .def("get_current_bfs_order", &MatrixGenerator<double>::getCurrentBFSOrder, "Get current BFS order")
        .def("hole_order", &MatrixGenerator<double>::holeOrder, py::arg("bfs_order"), py::arg("possible_holes"), "Get hole order")
        .def("is_scheduler_consistent", &MatrixGenerator<double>::isSchedulerConsistent, py::arg("scheduler"), "Is this scheduler consistent?");

    m.def("hint_convert", &hintConvert<double>, py::arg("result"), py::arg("old_reachable_states"), py::arg("new_reachable_states"), "Convert hint");
    m.def("set_end_components_true", &setEndComponentsTrue<double>, py::arg("hint"), "Set end components true");
    m.def("intersect_bitvectors", &intersect, py::arg("a"), py::arg("b"), "Intersect bitvectors");
}
