import Mathlib.MeasureTheory.Integral.Bochner.Basic
import SatUpper.Obligations
import Mathlib.Tactic.FinCases

/-! The explicit pair of survey marks and its numerical moments. -/

open MeasureTheory
open scoped ENNReal NNReal

namespace SatUpper.WitnessVertex

abbrev Mark := Fin 4 × Fin 4

noncomputable def markLaw : Measure Mark := (16 : ℝ≥0∞)⁻¹ • Measure.count

instance : IsProbabilityMeasure markLaw := by
  apply isProbabilityMeasure_iff.mpr
  norm_num [markLaw, Measure.count_apply_finite]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

def mark (a : Mark) : ℝ :=
  1 - (Formalization.badMass a.1 : ℝ) * (Formalization.badMass a.2 : ℝ)

theorem mark_bounds (a : Mark) : 0 ≤ mark a ∧ mark a ≤ 1 := by
  rcases a with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> norm_num [mark, Formalization.badMass]

theorem integral_mark_pow (j : ℕ) :
    (∫ a, mark a ^ j ∂markLaw) = (Formalization.markMoment j : ℝ) := by
  rw [markLaw, integral_smul_measure, integral_count]
  simp only [Formalization.markMoment, mark]
  push_cast
  rw [Fintype.sum_prod_type]
  norm_num
  ring

end SatUpper.WitnessVertex
