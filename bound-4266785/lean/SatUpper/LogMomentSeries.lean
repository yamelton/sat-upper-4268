import SatUpper.ReplicaMoments
import SatUpper.Series
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Dominated logarithmic moment series, uniformly away from the singularity. -/

open MeasureTheory

namespace SatUpper.LogMomentSeries

variable {Ω : Type*} [MeasurableSpace Ω]

theorem scaled_bounds {q z : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) : 0 ≤ q*z ∧ q*z ≤ q ∧ q*z < 1 := by
  have h := mul_le_of_le_one_right hq0 hz1
  exact ⟨mul_nonneg hq0 hz0, h, h.trans_lt hq1⟩

theorem hasSum_integral_log (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Z : Ω → ℝ} (hZ : Measurable Z) (h0 : ∀ x, 0 ≤ Z x) (h1 : ∀ x, Z x ≤ 1)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun r : ℕ => -(q^(r+1)/(r+1)) * (∫ x, (Z x)^(r+1) ∂μ))
      (∫ x, Real.log (1-q*Z x) ∂μ) := by
  have hs := Real.hasSum_pow_div_log_of_abs_lt_one
    (show |q| < 1 by rwa [abs_of_nonneg hq0])
  have hmeas (r : ℕ) : AEStronglyMeasurable
      (fun x => -(q^(r+1)/(r+1))*(Z x)^(r+1)) μ :=
    ((hZ.pow_const (r+1)).const_mul _).aestronglyMeasurable
  have hbound (r : ℕ) : ∀ᵐ x ∂μ,
      ‖-(q^(r+1)/(r+1))*(Z x)^(r+1)‖ ≤ q^(r+1)/(r+1) := by
    apply Filter.Eventually.of_forall
    intro x
    have ha : 0 ≤ q^(r+1)/(r+1) := by positivity
    have hz : 0 ≤ (Z x)^(r+1) := pow_nonneg (h0 x) _
    rw [norm_mul, Real.norm_eq_abs, abs_neg, abs_of_nonneg ha,
      Real.norm_eq_abs, abs_of_nonneg hz]
    exact mul_le_of_le_one_right ha (pow_le_one₀ (h0 x) (h1 x))
  have hlim : ∀ᵐ x ∂μ, HasSum
      (fun r : ℕ => -(q^(r+1)/(r+1))*(Z x)^(r+1)) (Real.log (1-q*Z x)) := by
    apply Filter.Eventually.of_forall
    intro x
    have hx := scaled_bounds hq0 hq1 (h0 x) (h1 x)
    have h := (Real.hasSum_pow_div_log_of_abs_lt_one
      (show |q*Z x| < 1 by rw [abs_of_nonneg hx.1]; exact hx.2.2)).neg
    convert h using 1
    · funext r
      rw [mul_pow]
      ring
    · simp
  have h := hasSum_integral_of_dominated_convergence
    (fun (r : ℕ) (_ : Ω) => q^(r+1)/(r+1)) hmeas hbound
    (Filter.Eventually.of_forall (fun _ => hs.summable)) (integrable_const _) hlim
  simpa only [integral_const_mul] using h

end SatUpper.LogMomentSeries
