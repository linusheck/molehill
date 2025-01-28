import os
import subprocess
import sys
from setuptools import setup, Extension
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
        subprocess.check_call([sys.executable, "-m", "ensurepip"])

        # Build pycarl
        pycarl_build = os.path.abspath(os.path.join(os.path.dirname(__file__), "build/pycarl"))
        self.update_git_repo("https://github.com/moves-rwth/pycarl.git", pycarl_build, "master")
        subprocess.check_call([sys.executable, "setup.py", "develop"], cwd=pycarl_build)

        pycarl_pybind_version = subprocess.check_output([sys.executable, "-c", "from pycarl._config import PYBIND_VERSION; print(PYBIND_VERSION)"]).decode().strip()

        # Build stormpy
        stormpy_build = os.path.abspath(os.path.join(os.path.dirname(__file__), "build/stormpy"))
        self.update_git_repo("https://github.com/moves-rwth/stormpy.git", stormpy_build, "master")
        subprocess.check_call([sys.executable, "setup.py", "develop"], cwd=stormpy_build)

        # Build paynt
        paynt_build = os.path.abspath(os.path.join(os.path.dirname(__file__), "build/paynt"))
        self.update_git_repo("https://github.com/lukovdm/synthesis.git", paynt_build, "master")
        subprocess.check_call(["git", "reset", "703a4ab72f927bdac41ff8ae3aa04768c8cea5f7", "--hard"], cwd=os.path.join(paynt_build))
        subprocess.check_call([sys.executable, "setup.py", "develop"], cwd=os.path.join(paynt_build))
        subprocess.check_call([sys.executable, "setup.py", "develop"], cwd=os.path.join(paynt_build, "payntbind"))

        build_temp = os.path.abspath(os.path.join(os.path.dirname(__file__), "build/fastmole"))
        os.makedirs(build_temp, exist_ok=True)

        extdir = os.path.abspath(os.path.dirname(self.get_ext_fullpath(ext.name)))
        cmake_args = [
            f"-DCMAKE_LIBRARY_OUTPUT_DIRECTORY={extdir}",
            f"-DPYBIND_VERSION={pycarl_pybind_version}",
            "-DCMAKE_EXPORT_COMPILE_COMMANDS=ON",
        ]

        subprocess.check_call(["cmake", ext.sourcedir] + cmake_args, cwd=build_temp)
        subprocess.check_call(["cmake", "--build", "."], cwd=build_temp)

setup(
    name="molehill",
    version="0.1.0",
    description="",
    author="Linus Heck <linus.heck@ru.nl>",
    packages=[],
    install_requires=[
        "z3-solver==4.13.3.0",
        "matplotlib==3.9.3",
        "pytest==8.3.4",
        "graphviz==0.20.3",
        "psutil==6.1.0"
    ],
    ext_modules=[CMakeExtension("fastmole", sourcedir=".")],
    cmdclass={"build_ext": CMakeBuild},
    build_system={
        'requires': ['setuptools', 'cmake', 'ninja'],
        'build-backend': 'setuptools.build_meta'
    }
)
