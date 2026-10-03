import SatUpper.Ground.Clause
import SatUpper.Ground.Bound
import SatUpper.PoissonCountMoments

/-! De-Poissonize the integer-energy mean using its one-clause bound. -/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SatUpper.ReplacementPoissonMean

theorem scaled_fixed_floor_le (n : ℕ) [NeZero n] {y : ℝ} (hy : 0 ≤ y) :
    (-y/n) * GroundFormula.mean n ⌊(Witness.alpha : ℝ)*n⌋₊ ≤
      Formalization.finiteAnalyticBound + (Witness.cutoff : ℝ)*Real.exp (-y) +
        y*(Real.sqrt ((Witness.alpha : ℝ)*n+1)/n) := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have h := PoissonCountMoments.fixed_floor_le
    (f := fun K => GroundComparison.mean n y K 0)
    (fun K => GroundComparison.clause_difference_bound hy K 0) (GroundBound.density*n)
  simp only [NNReal.coe_mul, NNReal.coe_natCast, GroundBound.density, NNReal.coe_mk] at h
  have hb := GroundBound.scaled_mean_le n hy
  simp only [DirectPoisson.expectation, DirectPoisson.zero_law, integral_dirac] at hb
  have hh := div_le_div_of_nonneg_right h hn.le
  rw [GroundClause.fixed_mean, add_div] at hh
  dsimp [GroundBound.density] at hb
  rw [div_mul_eq_mul_div]
  calc
    _ ≤ _ := hh
    _ ≤ _ := by rw [mul_div_assoc]; exact add_le_add_right hb _

end SatUpper.ReplacementPoissonMean
