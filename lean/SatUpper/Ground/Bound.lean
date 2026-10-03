import SatUpper.Ground.SiteBound
import SatUpper.Ground.Edge

/-! The energetic interpolation gives the certified trial bound. -/

open MeasureTheory
open scoped NNReal

namespace SatUpper.GroundBound

noncomputable def density : ℝ≥0 := ⟨(Witness.alpha : ℝ), by norm_num [Witness.alpha]⟩

theorem scaled_mean_le (n : ℕ) [NeZero n] {y : ℝ} (hy : 0 ≤ y) :
    DirectPoisson.expectation (GroundComparison.mean n y) (density*n) 0 / n ≤
      Formalization.finiteAnalyticBound + (Witness.cutoff : ℝ)*Real.exp (-y) := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have hr : (3*(density*n) : ℝ≥0)/(2*n : ℝ) = 3*(Witness.alpha : ℝ)/2 := by
    simp only [density, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_ofNat, NNReal.coe_mk]
    field_simp
  have h := GroundComparison.endpoint_comparison (n := n) hy (density*n)
  have hs := GroundSiteBound.endpoint (n := n) hy (3*(density*n)) hr Witness.cutoff
  have hh := div_le_div_of_nonneg_right (h.trans (sub_le_sub_right hs _)) hn.le
  have he := GroundEdge.correction_bound n y
  have he' :
      DirectPoisson.expectation (GroundComparison.mean n y) (density*n) 0 / n ≤
      negativeMomentSum Witness.cutoff Formalization.noWarningMoment +
        (Witness.cutoff : ℝ)*Real.exp (-y) -
        2*(Witness.alpha : ℝ)*GroundInsertion.edgeMean n y := by
    convert hh using 1
    unfold density
    push_cast
    field_simp
  unfold Formalization.finiteAnalyticBound
  linarith

end SatUpper.GroundBound
