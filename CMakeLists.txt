cmake_minimum_required(VERSION 3.23)
project(CDCL_Solver)

set(CMAKE_CXX_STANDARD 20)

add_executable(CDCL_Solver main.cpp SATSolver.cpp SATSolver.h CDCLSolver.cpp DPLLSolver.cpp)
