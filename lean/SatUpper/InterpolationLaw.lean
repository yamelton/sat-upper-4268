import SatUpper.PoissonConfiguration

/-! Uniform signed variables. -/

open MeasureTheory
open scoped ENNReal NNReal

namespace SatUpper.InterpolationLaw

noncomputable def signedVariableLaw (n : ℕ) : Measure (Fin n × Bool) :=
  ((Fintype.card (Fin n × Bool) : ℝ≥0∞))⁻¹ • Measure.count

instance (n : ℕ) [NeZero n] : IsProbabilityMeasure (signedVariableLaw n) := by
  apply isProbabilityMeasure_iff.mpr
  norm_num [signedVariableLaw, Measure.count_apply_finite]
  exact ENNReal.inv_mul_cancel (by simp [NeZero.ne n]) (ENNReal.mul_ne_top (by simp) (by norm_num))

end SatUpper.InterpolationLaw
