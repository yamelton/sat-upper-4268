# Random 3-SAT upper bound 4.268 — v1.0.0

By Fedor Vorobyev.

This release accompanies **A Lean-verified upper bound of 4.268 for random
3-SAT**. It proves asymptotic unsatisfiability for `floor(4.268*n)` independent
uniform signed clauses on three distinct variables per clause, allowing
repeated clauses.

- `sat-upper-4268.pdf`: the mathematical paper.
- `sat-upper-4268-arxiv.zip`: minimal LaTeX upload sources and generated bibliography.
- `sat-upper-4268-software-v1.0.0.zip`: Lean sources, independent rational
  certificate, tests, pinned dependencies, and verification records.
- `SHA256SUMS`: checksums for these artifacts.

The project was rebuilt from clean project artifacts with Lean 4.24.0.
The audit checked 233 theorem roots in 60 production modules and the exact
limit statement; its axiom union contains only `propext`, `Classical.choice`,
and `Quot.sound`. The audit-gate tests and numerical tests passed, and the
independent rational certificate reproduced exactly.

The software is Apache-2.0. **The paper is excluded from that license**;
its copyright is retained by Fedor Vorobyev. This release does not indicate
that the paper has been submitted to or announced by arXiv.
