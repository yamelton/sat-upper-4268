import SatKUpper.ClauseEndpoint
import SatKUpper.ModelTransfer
import SatUpper.PoissonCountMoments

/-! General-density transfer from a negative Poisson energy bound to legal k-SAT. -/

open MeasureTheory SatKUpper.Sampling
open scoped NNReal

namespace SatKUpper.DePoissonization

theorem fixed_floor_le {t r n : ℕ} [NeZero n] (law : CoinLaw t) {y : ℝ}
    (hy : 0 ≤ y) (α : ℝ≥0) :
    (-y/n)*Model.mean (r+1) n ⌊(α : ℝ)*n⌋₊ ≤
      (-y/n)*ClauseEndpoint.poissonMean (r+1) n (α*n) +
        y*(Real.sqrt ((α : ℝ)*n+1)/n) := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have h := SatUpper.PoissonCountMoments.fixed_floor_le
    (f := fun K => MeanComparison.mean law r n y K 0)
    (fun K => MeanComparison.clause_difference_bound law hy K 0) (α*n)
  simp only [NNReal.coe_mul, NNReal.coe_natCast] at h
  simp_rw [ClauseEndpoint.fixed_mean] at h
  rw [integral_const_mul] at h
  change -y*Model.mean (r+1) n ⌊(α : ℝ)*n⌋₊ ≤
    -y*ClauseEndpoint.poissonMean (r+1) n (α*n) + y*Real.sqrt ((α : ℝ)*n+1) at h
  have hh := div_le_div_of_nonneg_right h hn.le
  convert hh using 1 <;> ring

theorem countError_tendsto (α : ℝ≥0) :
    Filter.Tendsto (fun n : ℕ => Real.sqrt ((α : ℝ)*n+1)/n)
      Filter.atTop (nhds 0) := by
  have hi : Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have ht := ((hi.const_mul (α : ℝ)).add (hi.pow 2)).sqrt
  simp only [mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero, Real.sqrt_zero] at ht
  apply ht.congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have ha : 0 ≤ (α : ℝ)*n+1 := by positivity
  have he : (α : ℝ)*(n : ℝ)⁻¹ + ((n : ℝ)⁻¹)^2 =
      ((α : ℝ)*n+1)/(n : ℝ)^2 := by field_simp
  rw [he, Real.sqrt_div ha, Real.sqrt_sq (Nat.cast_nonneg n)]

/-- It remains to supply the explicit site evaluation to this probabilistic criterion. -/
theorem upperBound_of_poisson_bound {t r : ℕ} (law : CoinLaw t) (α : ℝ≥0)
    (T : ℕ) {B : ℝ} (hB : B < 0)
    (hbound : ∀ n : ℕ, 0 < n → ∀ y : ℝ, 0 < y →
      (-y/n)*ClauseEndpoint.poissonMean (r+1) n (α*n) ≤ B+(T : ℝ)*Real.exp (-y)) :
    Model.UpperBound (r+1) α := by
  have hδ : 0 < -B/4 := by linarith
  have ht : Filter.Tendsto (fun y : ℝ => (T : ℝ)*Real.exp (-y))
      Filter.atTop (nhds 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul (T : ℝ)
  obtain ⟨y, hy, he⟩ := ((Filter.eventually_gt_atTop (0 : ℝ)).and
    (ht.eventually_le_const hδ)).exists
  let c : ℝ := -B/(2*y)
  have hc : 0 < c := div_pos (neg_pos.mpr hB) (mul_pos (by norm_num) hy)
  apply ModelTransfer.upperBound_of_linear_mean (r+1) α.coe_nonneg hc
  have herror : Filter.Tendsto (fun n : ℕ => y*(Real.sqrt ((α : ℝ)*n+1)/n))
      Filter.atTop (nhds 0) := by simpa using (countError_tendsto α).const_mul y
  have herr := herror.eventually_le_const hδ
  filter_upwards [herr, Filter.eventually_ge_atTop 1] with n hn hnat
  letI : NeZero n := ⟨by omega⟩
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have h := (fixed_floor_le (r := r) (n := n) law hy.le α).trans
    (add_le_add_right (hbound n (by omega) y hy) _)
  apply (mul_le_mul_iff_right₀ (div_pos hy hnpos)).mp
  calc
    (y/n)*(c*n) = -B/2 := by dsimp [c]; field_simp
    _ ≤ (y/n)*Model.mean (r+1) n ⌊(α : ℝ)*n⌋₊ := by
      rw [neg_div, neg_mul] at h
      linarith

end SatKUpper.DePoissonization
