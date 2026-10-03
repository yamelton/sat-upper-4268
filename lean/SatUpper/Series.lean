import SatUpper.Local
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Analytic direction of the finite logarithmic-series certificate. -/

namespace SatUpper

theorem log_one_sub_le_neg_partial {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (K : ℕ) :
    Real.log (1 - x) ≤ - ∑ k ∈ Finset.range K, x ^ (k + 1) / (k + 1) := by
  have hs := Real.hasSum_pow_div_log_of_abs_lt_one
    (show |x| < 1 by rwa [abs_of_nonneg hx0])
  have hle := sum_le_hasSum (Finset.range K)
    (fun k _ => div_nonneg (pow_nonneg hx0 (k + 1)) (by positivity)) hs
  linarith

noncomputable def negativeMomentSum (K : ℕ) (μ : ℕ → ℝ) : ℝ :=
  - ∑ k ∈ Finset.range K, μ (k + 1) ^ 2 / (k + 1)

end SatUpper
