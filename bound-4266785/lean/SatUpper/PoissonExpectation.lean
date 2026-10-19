import SatUpper.Campbell
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-! Poisson expectations and summable exponential series for linearly growing functions. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

namespace SatUpper.PoissonExpectation

theorem factorial_weight_succ (t : ℝ) (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) * t ^ (n + 1) / ((n + 1).factorial : ℝ) =
      t * (t ^ n / (n.factorial : ℝ)) := by
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  field_simp

theorem summable_factorial_weight (t : ℝ) :
    Summable (fun n : ℕ => (n : ℝ) * t ^ n / (n.factorial : ℝ)) := by
  apply (summable_nat_add_iff 1).mp
  simp_rw [factorial_weight_succ]
  exact (NormedSpace.expSeries_div_hasSum_exp ℝ t).summable.mul_left t

theorem summable_linear_factorial (A B t : ℝ) :
    Summable (fun n : ℕ => (A + B * n) * t ^ n / (n.factorial : ℝ)) := by
  convert ((NormedSpace.expSeries_div_hasSum_exp ℝ t).summable.mul_left A).add
    ((summable_factorial_weight t).mul_left B) using 1
  funext n
  ring

theorem summable_exp_series_of_linear_growth {f : ℕ → ℝ} {A B : ℝ}
    (hg : ∀ n, ‖f n‖ ≤ A + B * n) (t : ℝ) :
    Summable (fun n => f n * t ^ n / (n.factorial : ℝ)) := by
  apply (summable_linear_factorial A B |t|).of_norm_bounded
  intro n
  rw [norm_div, norm_mul, norm_pow, Real.norm_eq_abs t, Real.norm_natCast]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hg n) (pow_nonneg (abs_nonneg t) n)) (Nat.cast_nonneg _)

/-- Exponential generating series, equal to the Poisson expectation at nonnegative rates. -/
noncomputable def poissonExpectation (f : ℕ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-t) * ∑' n, f n * t ^ n / (n.factorial : ℝ)

theorem linear_growth_of_bounded_increments {f : ℕ → ℝ} {C : ℝ}
    (hC : ∀ n, ‖f (n + 1) - f n‖ ≤ C) :
    ∀ n, ‖f n‖ ≤ ‖f 0‖ + C * n := by
  intro n
  have h := dist_le_range_sum_of_dist_le (f := f) (d := fun _ => C) n
    (fun {k} _ => by simpa only [dist_eq_norm, norm_sub_rev] using hC k)
  simp only [dist_eq_norm, norm_sub_rev, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  linarith [norm_sub_norm_le (f n) (f 0)]

theorem poissonExpectation_eq_tsum (f : ℕ → ℝ) (r : ℝ≥0) :
    poissonExpectation f r = ∑' n, poissonPMFReal r n * f n := by
  unfold poissonExpectation
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  unfold poissonPMFReal
  ring

theorem integrable_of_weighted {f : ℕ → ℝ} (r : ℝ≥0)
    (hs : Summable (fun n => poissonPMFReal r n * ‖f n‖)) :
    Integrable f (poissonMeasure r) := by
  refine ⟨(measurable_of_countable f).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm, lintegral_countable']
  have he (n : ℕ) : poissonMeasure r {n} = ENNReal.ofReal (poissonPMFReal r n) :=
    PMF.toMeasure_apply_singleton (poissonPMF r) n (measurableSet_singleton n)
  simp_rw [he, ← ENNReal.ofReal_mul (norm_nonneg _)]
  have hs' : Summable (fun n => ‖f n‖ * poissonPMFReal r n) := by
    simpa only [mul_comm] using hs
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun n => mul_nonneg (norm_nonneg (f n)) poissonPMFReal_nonneg) hs']
  exact ENNReal.ofReal_lt_top

theorem integral_eq_series {f : ℕ → ℝ} (r : ℝ≥0) (hi : Integrable f (poissonMeasure r)) :
    (∫ n, f n ∂poissonMeasure r) = ∑' n, poissonPMFReal r n * f n := by
  rw [poissonMeasure, PMF.integral_eq_tsum _ _ hi]
  change (∑' n, (ENNReal.ofReal (poissonPMFReal r n)).toReal * f n) = _
  simp_rw [ENNReal.toReal_ofReal poissonPMFReal_nonneg]

theorem integrable_poisson_of_linear_growth {f : ℕ → ℝ} {A B : ℝ}
    (hg : ∀ n, ‖f n‖ ≤ A + B * n) (r : ℝ≥0) : Integrable f (poissonMeasure r) := by
  have hnorm : ∀ n, ‖‖f n‖‖ ≤ A + B * n := by simpa only [norm_norm] using hg
  have hs : Summable (fun n => ‖f n‖ * poissonPMFReal r n) := by
    convert (summable_exp_series_of_linear_growth hnorm (r : ℝ)).mul_left (Real.exp (-(r : ℝ))) using 1
    funext n
    unfold poissonPMFReal
    ring
  apply integrable_of_weighted r
  simpa only [mul_comm] using hs

theorem poissonExpectation_eq_integral {f : ℕ → ℝ} {A B : ℝ}
    (hg : ∀ n, ‖f n‖ ≤ A + B * n) (r : ℝ≥0) :
    poissonExpectation f r = ∫ n, f n ∂poissonMeasure r := by
  rw [poissonExpectation_eq_tsum, integral_eq_series r (integrable_poisson_of_linear_growth hg r)]

end SatUpper.PoissonExpectation
