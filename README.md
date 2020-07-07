# isat - A simple SAT solver implemented in Idris 2

This is a very tiny SAT solver, loosely based on this tutorial: [Understanding SAT by Implementing a Simple SAT Solver in Python](https://sahandsaba.com/understanding-sat-by-implementing-a-simple-sat-solver-in-python.html).

The main goal is to experiment with Idris 2's [Linear Types](https://idris2.readthedocs.io/en/latest/tutorial/multiplicities.html#linearity).

The solver state (composed of watch list and current assignments) is kept in two
`LinArray`s which are threaded through the code using a linear state type (see
`Control/Linear/LState.idr`).

### Running

(A recent `idris2` needs to be installed and on your `$PATH`)

    make && make test

### Input Files

Input is expected in DIMACS format, e.g.:

```cnf
c This is a comment.
c Lines starting with "p " contain the problem description:
c Type (must be "cnf"), number of vars, number of clauses (ignored)
p cnf 3 4
1 2 -3 0
2 3 0
-2 0
-1 3 0
```

Two very tiny test files are included, bigger samples can be obtained from e.g.:
[SATLIB - Benchmark Problems](https://www.cs.ubc.ca/~hoos/SATLIB/benchm.html).
Some of the `.cnf` files there (for example the "uf..." collections) have a
weird `%\n0\n\n` at the end, which needs to be removed (`head -n -3` works).
The `flat...` collections from that URL work out of the box.
