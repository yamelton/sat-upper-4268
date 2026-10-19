# Random 3-SAT upper bound 4.268

**Fedor Vorobyev** · Independent researcher · fedorvorobev@gmail.com

Lean 4 proof that an iid uniform random signed 3-CNF formula with
`floor(1067*n/250)` clauses is unsatisfiable with probability tending to one.
Each clause uses three distinct variables; repeated clauses are allowed.
No existence or exact value of a limiting threshold is assumed.

The mathematical paper is [paper/main.tex](paper/main.tex).
Download the PDF and arXiv source bundle from the
[release page](https://github.com/yamelton/sat-upper-4268/releases).
The software-only archive contains the proof and verification tools; the
full repository also contains the manuscript and paper build tools.

## Reproduce the theorem

Install [elan](https://github.com/leanprover/elan) and Python 3.10–3.13
(the numerical suite is tested with Python 3.13). The committed toolchain
and Lake manifest pin Lean 4.24.0 and mathlib revision
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`.

```sh
sh lean/run.sh exe cache get
python3 lean/verify.py
python3 lean/test_verify.py
```

`verify.py` builds the project, inventories 233 theorems in 60 modules,
audits their transitive axiom dependencies, and checks the expanded public
endpoint. The only allowed axioms are `propext`, `Classical.choice`, and
`Quot.sound`. Kernel arithmetic proves the rational certificate; neither
Python nor native evaluation is a numerical oracle for the theorem.
The wrapper uses an optional project-local `.tools/elan` installation if
present; a normal fresh checkout uses elan from `PATH`.

The endpoint is

```lean
Filter.Tendsto
  (fun n : Nat => SatUpper.satisfiabilityProbability n (1067*n/250))
  Filter.atTop (nhds 0)
```

See [the model](lean/SatUpper/Model.lean),
[the final theorem](lean/SatUpper/Threshold.lean), and
[the targeted review](publication/AUDIT.md).

## Independent certificate and tests

The rational certificate needs only Python's standard library:

```sh
python3 src/richer_certificate.py --alpha 4.268 --cutoff 128 \
  --surveys .05,.85,.5 .4,.4,.5 --output certificate.json
```

To run all checks, including numerical cross-checks:

```sh
python3 -m venv .venv
.venv/bin/python -m pip install -r requirements.txt
.venv/bin/python scripts/check.py
```

This rebuilds and audits Lean, exercises the audit gate, runs the inherited
numerical tests, and reproduces the exact certificate. A successful run
writes `results/release-checks.json` with hashes of its inputs.
`--skip-lean` can reuse an audit only if its recorded source hashes match.
Historical scalar-witness tests retain two small certificate fixtures;
these are regression tests, not additional hypotheses of the 4.268 proof.

The warning rate law has atoms `1/20`, `2/5`, `17/20` with probabilities
`1/4`, `1/2`, `1/4`. At cutoff 128 the independent rational upper bound
is approximately `-0.000011202545238429759`. Lean independently proves
the bound `<= -1/100000` using analytic enclosures and kernel reduction.

## Build the paper and bundles

From the full repository, install a LaTeX distribution providing PDFLaTeX,
BibTeX, the standard AMS packages, Latin Modern, geometry, hyperref, and
microtype. Then run:

```sh
python3 scripts/build_paper.py
python3 scripts/package.py
```

The paper build rejects unresolved references and overfull boxes.
Packaging requires successful, current verification reports. It produces
the PDF, a minimal arXiv LaTeX source archive including the generated
bibliography, a software-only archive, and checksums in `dist/`.
No dependency cache, toolchain binary, credential, or development archive
is included. CI repeats the checks from a checkout on Linux.

## Attribution and licensing

Use [CITATION.cff](CITATION.cff) to cite the software. Mathematical
attribution to Franz–Leone, Panchenko–Talagrand, Lelarge–Oulamara, and
related work is given in the paper. The argument proves its needed
inequalities directly rather than treating cited papers as Lean assumptions.

Original software is **Apache-2.0**. The **manuscript is excluded** from
that grant; its copyright is retained by Fedor Vorobyev. See
[NOTICE](NOTICE) for the precise scope and third-party attribution.

The production Lean sources are preserved from `sat_upper_elegance`;
[source-manifest.json](publication/source-manifest.json) records their
snapshot hashes. The publication work changes the packaging and audit
reporting, not the theorem or its proof terms.
