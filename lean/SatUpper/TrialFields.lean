import SatUpper.WitnessVertex
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! Bernoulli cavity warnings, using mathlib's probability mass function. -/

open MeasureTheory

namespace SatUpper.TrialFields

theorem badMass_bounds (i : Fin 4) :
    0 ≤ (Formalization.badMass i : ℝ) ∧ (Formalization.badMass i : ℝ) < 1 := by
  fin_cases i <;> norm_num [Formalization.badMass]

noncomputable def stateLaw (i : Fin 4) : Measure Bool :=
  (PMF.bernoulli ⟨(Formalization.badMass i : ℝ), (badMass_bounds i).1⟩
    (by change (Formalization.badMass i : ℝ) ≤ 1; exact (badMass_bounds i).2.le)).toMeasure

instance (i : Fin 4) : IsProbabilityMeasure (stateLaw i) := by
  unfold stateLaw
  infer_instance

theorem stateLaw_hard (i : Fin 4) :
    (stateLaw i).real {true} = (Formalization.badMass i : ℝ) := by
  rw [measureReal_def, stateLaw, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp

abbrev InnerMark := Bool × Bool

noncomputable def messageLaw (a : WitnessVertex.Mark) : Measure InnerMark :=
  (stateLaw a.1).prod (stateLaw a.2)

instance (a : WitnessVertex.Mark) : IsProbabilityMeasure (messageLaw a) := by
  unfold messageLaw
  infer_instance

theorem messageLaw_hard (a : WitnessVertex.Mark) :
    (messageLaw a).real {(true,true)} =
      (Formalization.badMass a.1 : ℝ) * (Formalization.badMass a.2 : ℝ) := by
  rw [measureReal_def, messageLaw, ← Set.singleton_prod_singleton, Measure.prod_prod,
    ENNReal.toReal_mul]
  exact congrArg₂ (· * ·) (stateLaw_hard a.1) (stateLaw_hard a.2)

end SatUpper.TrialFields
