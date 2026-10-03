import SatUpper.ReplacementAsymptotic
import SatUpper.NumericalEnclosure
import Mathlib.Algebra.Order.Floor.Semifield

/-! Transfer the Poisson comparison to the fixed clause count.
Distinct variables are handled by `LegalConditioning` at the probability level. -/

open Filter
open scoped Topology

namespace SatUpper.ModelTransfer

theorem floor_alpha_eq (n : ℕ) : ⌊(Witness.alpha : ℝ)*n⌋₊ = clauseCount n := by
  simpa [Witness.alpha, clauseCount, div_mul_eq_mul_div] using
    (Nat.floor_div_eq_div (K := ℝ) (1067*n) 250)

theorem asymptoticComparison : Formalization.AsymptoticComparison := by
  intro y hy δ hδ
  have ht := ReplacementAsymptotic.countError_tendsto.const_mul y
  simp only [mul_zero] at ht
  filter_upwards [ht.eventually_le_const hδ, eventually_ge_atTop 1] with n he hn
  letI : NeZero n := ⟨by omega⟩
  have h := ReplacementPoissonMean.scaled_fixed_floor_le n hy.le
  rw [floor_alpha_eq] at h
  change y*(Real.sqrt ((Witness.alpha : ℝ)*n+1)/n) ≤ δ at he
  linarith

end SatUpper.ModelTransfer
