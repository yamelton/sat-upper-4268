# Random 3-SAT upper bound: 4.266785

This revision uses the continuous coin density

    rho(r) = (140/1989) (1-r)^(1/3) (24-34r+37r^2),  0 < r < 1.

The target theorem says that the satisfiability probability tends to zero for
`floor(853357*n/200000)` independently sampled, uniformly random signed
3-clauses with distinct variables within each clause. Repeated clauses are
allowed.

## Verification status

The compact certificate uses a degree-192 polynomial lower bound for
`-log(1-x)`, with 192 site moments and 512 correction terms. Its exact rational
calculation and an independent 420-digit Decimal calculation agree. The full Lean proof and axiom audit pass; the authoritative result is
`results/lean-verification.json`. The audit permits only `Classical.choice`,
`Quot.sound`, and `propext`, and rejects proof placeholders and additional axioms.

The density, moments, and correction tail are proved in
`lean/SatFinal/Quadratic.lean`. The polynomial satisfies `P(0) = 0` and
`P'(x) = 2R(x) - (1-x)R(x)^2`. Thus

    (-log(1-x) - P(x))' = (1-(1-x)R(x))^2 / (1-x) >= 0.

`PolynomialLog.lean` and `PolynomialCriterion.lean` connect this inequality to
the SAT bound. Every coefficient identity and numerical enclosure is checked
by Lean's kernel. `lean/SatFinal/Endpoint.lean` states the exact natural-number
clause count.

## Reproduce the proof

Install the Lean version in `lean/lean-toolchain` using elan. The mathlib
revision and its dependencies are pinned in `lean/lake-manifest.json`.
From the release root:

```sh
sh lean/run.sh exe cache get
python3 lean/verify.py
python3 lean/test_verify.py
```

The verifier builds the complete project import closure from source; it uses
mathlib's pinned cache. It compiles with one worker by default;
`SAT_BUILD_WORKERS=2` enables two concurrent compiler processes. Progress is
recorded in `results/build-status.json`.
A build checkpoint is reused only when source, dependency, and object hashes
match. Delete `results/build-cache.json` to force all project modules to rebuild.
The final audit checks the exact probability statement and the transitive
axioms of every new theorem, rejecting additional axioms or proof placeholders.

Local development can reuse dependency caches through symlinks. The source
archive excludes those symlinks, compiled objects, toolchains, and caches.

## Reproduce the independent calculation

```sh
python3 certificate/certify_polynomial.py
```

This uses only Python's standard library. It checks outward rational bounds
and independently evaluates closed-form moments and direct binomial sums with
420-digit Decimal arithmetic. The rational upper bound is
`-711954580248631/1208925819614629174706176`. Lean's witness uses slightly
different outward rounding and gives
`-711954580246485/1208925819614629174706176`. Both are below `-4e-10`.

The original direct Taylor calculation, with T = 5120 and H = 512, is also
retained for the manuscript:

```sh
python3 certificate/certify_compact.py
```

Its independent C++ cross-check requires a C++17 compiler, GMP, and MPFR.
`CXX` selects the compiler; `pkg-config mpfr` supplies library flags when
available. The optional `--check-only` flag reruns the MPFR comparison against
the saved rational certificate. These independent checks are not premises of
the Lean proof.

## Regenerate numerical proof data

The checked-in tables suffice for verification. To regenerate them:

```sh
python3 generate_polynomial_witness.py
python3 lean/verify.py
```

The witness data is about 1.2 MB. Polynomial coefficient checks are split into
small blocks to bound compiler memory. The rational polynomial seed is
untrusted data: its selection does not affect the proof's trust assumptions.
All generated inequalities and identities must pass the kernel checks.

## Publication history

This software release certifies the improved bound 4.266785. The accompanying
manuscript revision will be published separately. The original 4.268 proof
and manuscript remain available in release v1.0.0:
https://github.com/yamelton/sat-upper-4268/releases/tag/v1.0.0 and
https://doi.org/10.5281/zenodo.23120101.

Software is licensed under Apache-2.0; see LICENSE and NOTICE. The manuscript
is excluded from the software license; its copyright remains with Fedor
Vorobyev.
