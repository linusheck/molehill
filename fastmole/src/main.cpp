#include <string>
#include <vector>
#include <pybind11/pybind11.h>
#include <pybind11/stl.h>
#include "storm/adapters/RationalFunctionAdapter.h"
#include "storm/storage/SparseMatrix.h"
#include "storm/storage/BitVector.h"
#include "storm/utility/graph.h"

namespace py = pybind11;

py::module_ storage = py::module_::import("stormpy.storage");


std::string helloWorld() {
    return "Hello, World!";
}

PYBIND11_MODULE(fastmole, m) {
    m.doc() = R"pbdoc(
        Fastmole: molehill's fast algorithms
        -----------------------
        .. currentmodule:: fastmole
        .. autosummary::
           :toctree: _generate
    )pbdoc";

    m.def("hello", &helloWorld, R"pbdoc(
        Return a string "Hello, World!".
    )pbdoc");

    m.def("submatrix", [](storm::storage::SparseMatrix<double> const& matrix, storm::storage::BitVector const& rowConstraint, storm::storage::BitVector const& columnConstraint, bool insertDiagonalEntries = false, bool useGroups = true) {
        return matrix.getSubmatrix(useGroups, rowConstraint, columnConstraint, insertDiagonalEntries);
    }, py::arg("matrix"), py::arg("row_constraint"), py::arg("column_constraint"), py::arg("insert_diagonal_entries") = false, py::arg("use_groups") = true, "Get submatrix");

    m.def("submatrix", [](storm::storage::SparseMatrix<storm::RationalFunction> const& matrix, storm::storage::BitVector const& rowConstraint, storm::storage::BitVector const& columnConstraint, bool insertDiagonalEntries = false, bool useGroups = true) {
        return matrix.getSubmatrix(useGroups, rowConstraint, columnConstraint, insertDiagonalEntries);
    }, py::arg("matrix"), py::arg("row_constraint"), py::arg("column_constraint"), py::arg("insert_diagonal_entries") = false, py::arg("use_groups") = true, "Get submatrix");


    m.def("test", [](storm::storage::BitVector const& test) {
        return test;
    }, py::arg("test"), "Test");
    m.def("test2", [](storm::storage::SparseMatrix<double> const& test) {
        return test;
    }, py::arg("test2"), "Test2");
    m.def("test3", []() {
        return storm::storage::BitVector(10);
    },"Test3");


}