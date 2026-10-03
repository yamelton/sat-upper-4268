import SatUpper.ReplacementPoissonMean

/-! The Poisson count error vanishes after normalization. -/

open Filter
open scoped Topology

namespace SatUpper.ReplacementAsymptotic

noncomputable def countError (n : ℕ) : ℝ :=
  Real.sqrt ((Witness.alpha : ℝ)*n+1)/n

theorem countError_tendsto : Tendsto countError atTop (𝓝 0) := by
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have ht := ((hi.const_mul (Witness.alpha : ℝ)).add (hi.pow 2)).sqrt
  simp only [mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero, Real.sqrt_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have ha : 0 ≤ (Witness.alpha : ℝ)*n+1 := by
    have : (0 : ℝ) ≤ Witness.alpha := by norm_num [Witness.alpha]
    positivity
  have he : (Witness.alpha : ℝ)*(n : ℝ)⁻¹ + ((n : ℝ)⁻¹)^2 =
      ((Witness.alpha : ℝ)*n+1)/(n : ℝ)^2 := by field_simp
  rw [he, Real.sqrt_div ha, Real.sqrt_sq (Nat.cast_nonneg n)]
  unfold countError
  ring

end SatUpper.ReplacementAsymptotic
