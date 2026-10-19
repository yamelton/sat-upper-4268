# Random 3-SAT upper bound 4.266785

**Fedor Vorobyev** · Independent researcher · fedorvorobev@gmail.com

The new Lean development proves that the satisfiability probability tends
to zero for `floor(853357*n/200000)` iid uniform signed 3-clauses on `n`
variables, with distinct variables within each clause. Repeated clauses
are allowed; no existence of a limiting threshold is assumed.

The complete proof, numerical witnesses, independent certificate, audit
report, and reproduction instructions are in
[bound-4266785/](bound-4266785/README.md).

```sh
cd bound-4266785
sh lean/run.sh exe cache get
python3 lean/verify.py
python3 lean/test_verify.py
python3 certificate/certify_polynomial.py
```

Lean checks the rational certificate in its kernel. The transitive axiom
audit permits only `propext`, `Classical.choice`, and `Quot.sound`.
The compact certificate uses 192 site moments and a polynomial logarithm
minorant. Independent rational and 420-digit Decimal calculations agree;
they are cross-checks, not premises of the theorem.

The [v2.0.0 release](https://github.com/yamelton/sat-upper-4268/releases/tag/v2.0.0)
contains the software-only source archive. The manuscript revision will
be published separately.

The original 4.268 development remains in the root `lean/`, `src/`, and
`paper/` directories and in the
[v1.0.0 release](https://github.com/yamelton/sat-upper-4268/releases/tag/v1.0.0).
Its [original README](publication/README-v1.md) and
[archival DOI](https://doi.org/10.5281/zenodo.23120101) describe that version.

Original software is Apache-2.0; see the applicable LICENSE and NOTICE
files. The manuscript is excluded from that grant. Use
[CITATION.cff](CITATION.cff) to cite the new software release.
