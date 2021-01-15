# short-proof

A SAT-based tool to compute shortest proofs of propositional and QBF formulas in resolution-based proof systems.
For propositional formulas, the shortest resolution proof is computed.
For QBFs, the default proof system is Q-resolution, but long-distance Q-resolution or reductionless long-distance Q-resolution can also be specified.
Support for QBFs is still experimental, please report any issues found.

Requires Python 3.6+ and [PySAT](https://pysathq.github.io/).

Usage: `./short.py <cnf.dimacs>` (you may need to make the file executable).

Use `--query s F` to output a CNF formula `short_s(F)` that encodes the question whether F has a resolution refutation of length at most s.

See `./short.py -h` for more options. In particular, `-v` may be useful to see intermediate lower bounds.
