#include <string>
#include <vector>
#include <pybind11/pybind11.h>
#include <pybind11/stl.h>

#include "MatrixGenerator.h"

#include "storm/adapters/RationalFunctionAdapter.h"
#include "storm/storage/SparseMatrix.h"
#include "storm/storage/BitVector.h"
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

    // m.def("hello", &helloWorld, R"pbdoc(
    //     Return a string "Hello, World!".
    // )pbdoc");

    m.def("submatrix", [](storm::storage::SparseMatrix<double> const& matrix, storm::storage::BitVector const& rowConstraint, storm::storage::BitVector const& columnConstraint, bool insertDiagonalEntries = false, bool useGroups = true) {
        return matrix.getSubmatrix(useGroups, rowConstraint, columnConstraint, insertDiagonalEntries);
    }, py::arg("matrix"), py::arg("row_constraint"), py::arg("column_constraint"), py::arg("insert_diagonal_entries") = false, py::arg("use_groups") = true, "Get submatrix");

    m.def("submatrix", [](storm::storage::SparseMatrix<storm::RationalFunction> const& matrix, storm::storage::BitVector const& rowConstraint, storm::storage::BitVector const& columnConstraint, bool insertDiagonalEntries = false, bool useGroups = true) {
        return matrix.getSubmatrix(useGroups, rowConstraint, columnConstraint, insertDiagonalEntries);
    }, py::arg("matrix"), py::arg("row_constraint"), py::arg("column_constraint"), py::arg("insert_diagonal_entries") = false, py::arg("use_groups") = true, "Get submatrix");

    // Create bindings for MatrixGenerator
    py::class_<MatrixGenerator<double>>(m, "MatrixGenerator")
        .def(py::init<storm::storage::SparseMatrix<double> const&, std::vector<double> const&>())
        .def("build_matrix", &MatrixGenerator<double>::buildMatrix, py::arg("quotient_state_map"), py::arg("sub_mdp_matrix"), py::arg("included_choices"), "Build matrix")
        .def("build_state_labeling", &MatrixGenerator<double>::buildStateLabeling, py::arg("sub_mdp_matrix"), py::arg("sub_mdp_labeling"), py::arg("one_states"), "Build state labeling");
}