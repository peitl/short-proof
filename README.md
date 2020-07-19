# short-proof

A SAT-based tool to compute shortest resolution proofs.

Requires Python 3.6+ and [PySAT](https://pysathq.github.io/).

Usage: `./short.py <cnf.dimacs>` (you may need to make the file executable).

Use `--query s F` to output a CNF formula `short_s(F)` that encodes the question whether F has a resolution refutation of length at most s.

See `./short.py -h` for more options. In particular, `-v` may be useful to see intermediate lower bounds.
