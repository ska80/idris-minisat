all: isat

isat:
	idris2 --build isat.ipkg

clean:
	rm -rf build

test: isat
	build/exec/isat tests/sat/first.cnf
	build/exec/isat tests/sat/color.cnf

.PHONY: all clean isat
