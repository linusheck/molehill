import os
import subprocess
import sys
from setuptools import Extension
from setuptools.command.build_ext import build_ext


class CMakeExtension(Extension):
    def __init__(self, name, sourcedir=""):
        super().__init__(name, sources=[])
        self.sourcedir = os.path.abspath(sourcedir)


class CMakeBuild(build_ext):

    def update_git_repo(self, remote, folder, branch):
        if not os.path.exists(folder):
            subprocess.check_call(["git", "clone", remote, folder, "--branch", branch])
        else:
            subprocess.check_call(["git", "fetch"], cwd=folder)
            subprocess.check_call(["git", "reset", "--hard", f"origin/{branch}"], cwd=folder)

    def build_extension(self, ext):
        print("sys executable", sys.executable)
        # install setuptools (poetry does not install it)
        subprocess.check_call([sys.executable, "-m", "ensurepip"])
        # subprocess.check_call([sys.executable, "-m", "pip", "install", "setuptools"])

        # build pycarl
        pycarl_build = os.path.abspath(os.path.join(os.path.dirname(__file__), "build/pycarl"))
        self.update_git_repo("https://github.com/moves-rwth/pycarl.git", pycarl_build, "master")
        subprocess.check_call([sys.executable, "setup.py", "develop"], cwd=pycarl_build)

        # print(sys.executable)
        # pycarl_pybind_version = subprocess.check_output([sys.executable, "-c", "import sys; print(sys.executable); from pycarl._config import PYBIND_VERSION; print(PYBIND_VERSION)"]).decode().strip()
        pycarl_pybind_version = "2.10.0" # TODO hardcoded

        # # verify that pybind11 is present (pycarl should have installed it, and we will be using it further)
        # try:
        #     import pybind11
        # except ImportError:
        #     raise ImportError("pybind11 is required to build the fastmole extension (stormpy should have installed it!)")

        # build stormpy
        stormpy_build = os.path.abspath(os.path.join(os.path.dirname(__file__), "build/stormpy"))
        self.update_git_repo("https://github.com/moves-rwth/stormpy.git", stormpy_build, "master")
        subprocess.check_call([sys.executable, "setup.py", "develop"], cwd=stormpy_build)

        build_temp = os.path.abspath(os.path.join(os.path.dirname(__file__), "build/fastmole"))
        os.makedirs(build_temp, exist_ok=True)

        extdir = os.path.abspath(os.path.dirname(self.get_ext_fullpath(ext.name)))
        cmake_args = [
            f"-DCMAKE_LIBRARY_OUTPUT_DIRECTORY={extdir}",
            f"-DPYBIND_VERSION={pycarl_pybind_version}",
        ]

        # Run CMake configure and build
        subprocess.check_call(["cmake", ext.sourcedir] + cmake_args, cwd=build_temp)
        subprocess.check_call(["cmake", "--build", "."], cwd=build_temp)

def build(setup_kwargs):
    setup_kwargs.update({
        "ext_modules": [CMakeExtension("fastmole", sourcedir=".")],
        "cmdclass": {"build_ext": CMakeBuild},
    })
