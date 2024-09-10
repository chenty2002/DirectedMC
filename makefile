all: dmc

dmc: DMC.hpp aig.hpp basic.hpp sat_solver.hpp ipasir.h libcadical.a minisat/build/dynamic/lib/libminisat.so
	g++ -std=c++0x -O3 -o dmc DMC.cpp aig.cpp main.cpp -g \
		-L. -lcadical \
		-Iminisat  -Iminisat/minisat/simp -Iminisat/minisat/core -Iminisat/minisat/mtl minisat/build/release/lib/libminisat.a

clean:
	rm dmc