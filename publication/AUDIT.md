# Targeted publication review

This records the assistant's source and mathematical review, not an external
referee report. Lean's checks and the independent numerical tests are
separate evidence. The author must assess the manuscript as a scholarly work.

## Model and endpoint

- `Model.lean` uses finite-cardinality ratios for iid ordered clauses with an
  injective three-variable map and independent Boolean falsifying signs.
  Entire clauses may repeat. Each unordered legal clause has six ordered
  representations; their multiplicities do not depend on signs or variables.
- `clauseCount` is natural division `1067*n/250`, not rounding to nearest.
  `ModelTransfer.floor_alpha_eq` establishes the correspondence to the real floor.
- The expanded limit in `Threshold.lean` is checked explicitly by the audit.
  No extra comparison or numerical hypothesis remains at this endpoint.
- The empty legal clause space for `n < 3` affects finitely many indices only.
  The paper restricts its probabilistic model to `n >= 3` and explains Lean's
  totalized definition for smaller indices.

## Central argument

- `Ground/Minimum`: integrality is essential to the exact insertion identity.
  If every old minimizer violates the inserted unit predicate, all competing
  assignments already cost at least one more. This is not a continuous-energy lemma.
- `Ground/Finite` and `Direct/Finite`: the inner average is over Boolean
  warning arrays at fixed rows. Rows, rates, and signs are averaged after
  the logarithm. The manuscript preserves this order.
- `Ground/Insertion`: universal quantifiers over minimizers and the three
  literal positions commute, even for repeated variable positions. Site
  warnings are freshly averaged before taking the ratio. The tilted law
  is a probability law and the moment is positive.
- `LogInsertion` and `ReplicaCubic`: the same replica environment is used
  in all three moments. Fresh seeds are independent across the three
  positions. Nonnegative features give `(B-C)^2*(B+2*C) >= 0`; logarithmic
  coefficients have the required nonpositive sign.
- `BinomialPoisson` and `Ground/Comparison`: the finite replacement recurrence
  uses coefficients 1, 2, 3. The Poisson Cauchy product gives means `a` and
  `3*a` and correction `-2*a*d`. Bounded increments ensure absolute convergence.
- `Ground/Site` and `SiteSideLaw`: the site estimate counts conflicting
  variables; it does not claim equality with minimum energy. The map grouping
  warning coordinates is injective across both signs and all variables.
- `PoissonPair`: mixed moments come from disjoint sign classes. The finite
  softened-log bound includes the boundary `G = 0`; the proof does not require
  integrability of `log G` or `1/G`.
- `ReplacementPoissonMean`, `Obligations`, `FiniteVariance`, and
  `LegalConditioning`: fix one finite softening parameter first. The floor
  error is bounded by `sqrt(alpha*n+1)`, variance by the clause count, and
  conditioning costs at most `exp(6*alpha)` for `n >= 6`.

## Arithmetic and dependency evidence

- `GridExponential` starts from tangent/reciprocal exponential bounds, then
  rounds outward after squaring. `NumericalMoments` computes all intervals
  inside Lean, rather than accepting an externally generated table.
- Signed moment enclosures and clamping before squaring preserve the upper
  bound on the negative vertex contribution. The negative edge multiplier
  reverses the logarithmic lower bound as required.
- The final rational comparison uses `decide +kernel`.
- All 60 production modules belong to the import closure of `Threshold`.
  The audit covers 233 theorem roots, including the fractional-moment bridge.
  No production `axiom`, `sorry`, or `admit` declaration was found in the
  source review; the decisive check is the transitive kernel axiom audit.
- A fresh build of project modules passed using a separately copied pinned
  dependency cache. The independent Python certificate reproduced exactly.
  Current machine-readable evidence is in `results/lean_verification.json`
  and `results/release-checks.json`; hashes distinguish fresh evidence from
  stale historical reports.

## Literature and category

- [Franz–Leone](https://arxiv.org/abs/cond-mat/0208280), Section III.B:
  clause/site comparison and nested partition moments. The cited preprint's
  odd-arity discussion is conditional. The paper explicitly proves its own
  cubic sign and does not claim to identify its law with equation (46).
- [Panchenko–Talagrand](https://arxiv.org/abs/math/0405357): broader bounds
  for diluted models; mathematical context, not an imported proof premise.
- [Lelarge–Oulamara](https://arxiv.org/html/1708.02457v2), condition (4) and
  equation (30): nonnegative features and the polynomial remainder.
- [Mertens–Mézard–Zecchina](https://arxiv.org/abs/cs/0309020): cavity-method
  threshold predictions, distinguished from the proved endpoint here.
- [Díaz et al.](https://arxiv.org/abs/0807.3600): the stated historical 4.4898
  bound. The paper does not label that number the current best bound.
- Chosen primary category: **math.PR**; requested cross-list: **cs.DM**.
  This follows the probabilistic comparison argument and its closest
  mathematical precedents. Formal verification is supporting evidence.

This targeted review does not establish a priority claim or replace an
exhaustive literature review. No substantive mathematical discrepancy was
identified in the reviewed chain. No production Lean proof was changed.

## Publication changes

The Python pins were changed to installable versions tested on Python 3.13:
NumPy 2.2.6, SciPy 1.15.3, and mpmath 1.3.0. The audit report now records
source hashes. Packaging checks their freshness and excludes local caches.
The paper includes the precise model, sign qualifications, finite arithmetic
recipe, and a software/manuscript license distinction.
