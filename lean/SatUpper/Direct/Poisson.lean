import SatUpper.BinomialPoisson

/-! A Poisson endpoint comparison from finite binomial replacements. -/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace SatUpper.DirectPoisson

theorem zero_law : poissonMeasure 0 = Measure.dirac 0 := by
  apply Measure.ext_of_singleton
  intro K
  rw [poissonMeasure, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton K)]
  change ENNReal.ofReal (poissonPMFReal 0 K) = _
  cases K <;> simp [poissonPMFReal]

noncomputable def expectation (f : ℕ → ℕ → ℝ) (r s : ℝ≥0) : ℝ :=
  ∫ K, ∫ L, f K L ∂poissonMeasure s ∂poissonMeasure r

variable {f : ℕ → ℕ → ℝ} {C : ℝ}

theorem integrable_row (hS : ∀ K L, ‖f K (L+1)-f K L‖ ≤ C) (s : ℝ≥0) (K : ℕ) :
    Integrable (f K) (poissonMeasure s) :=
  PoissonExpectation.integrable_poisson_of_linear_growth
    (PoissonExpectation.linear_growth_of_bounded_increments (hS K)) s

/-- Replace a site by a clause with probability 1/3 and an empty slot otherwise. -/
theorem comparison (hC : ∀ K L, ‖f (K+1) L-f K L‖ ≤ C)
    (hS : ∀ K L, ‖f K (L+1)-f K L‖ ≤ C) {d : ℝ}
    (h : ∀ K L, f (K+1) L-f K L - 3*(f K (L+1)-f K L) + 2*d ≤ 0)
    (a : ℝ≥0) :
    expectation f a 0 ≤ expectation f 0 (3*a) - 2*a*d := by
  have hc := BinomialPoisson.comparison hC hS (fun K L => by linarith [h K L]) a
  have hgC := PoissonExpectation.linear_growth_of_bounded_increments
    (f := fun K => f K 0) (fun K => hC K 0)
  have hgS := PoissonExpectation.linear_growth_of_bounded_increments (hS 0)
  have hs := PoissonExpectation.poissonExpectation_eq_integral hgS (3*a)
  simp only [NNReal.coe_mul, NNReal.coe_ofNat] at hs
  rw [PoissonExpectation.poissonExpectation_eq_integral hgC a, hs] at hc
  simpa only [expectation, zero_law, integral_dirac] using hc

end SatUpper.DirectPoisson
