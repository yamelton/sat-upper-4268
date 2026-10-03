import SatUpper.ConditionalArrays
import SatUpper.ClauseEndpoint
import SatUpper.Concentration
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Finite uniform averages agree with normalized counting-measure integrals. -/

open MeasureTheory
open scoped ENNReal

namespace SatUpper.FiniteUniformLaw

variable (A : Type*) [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]

noncomputable def law : Measure A := (Fintype.card A : ℝ≥0∞)⁻¹ • Measure.count

theorem integral_law (f : A → ℝ) : (∫ a, f a ∂law A) = uniformAverage f := by
  classical
  rw [law, integral_smul_measure, integral_count]
  simp [uniformAverage, ENNReal.toReal_inv, div_eq_mul_inv, mul_comm]

instance [Nonempty A] : IsProbabilityMeasure (law A) := by
  classical
  apply isProbabilityMeasure_iff.mpr
  simp only [law, Measure.smul_apply, smul_eq_mul]
  rw [Measure.count_apply_finite]
  simpa using ENNReal.inv_mul_cancel
    (show (Fintype.card A : ℝ≥0∞) ≠ 0 by simp [Fintype.card_ne_zero])
    (show (Fintype.card A : ℝ≥0∞) ≠ ∞ by simp)
  exact Set.finite_univ

theorem pi_law [Nonempty A] (I : Type*) [Fintype I] [DecidableEq I] :
    Measure.pi (fun _ : I => law A) = law (I → A) := by
  classical
  apply Measure.ext_of_singleton
  intro x
  rw [ConditionalArrays.pi_singleton]
  simp [law, Measure.smul_apply, smul_eq_mul, ENNReal.inv_pow]

theorem clauseLaw_eq (n : ℕ) [NeZero n] :
    ClauseEndpoint.clauseLaw n = law (ClauseEndpoint.Clause n) :=
  pi_law (Fin n × Bool) (Fin 3)

theorem clause_family_integral (n K : ℕ) [NeZero n] (f : (Fin K → ClauseEndpoint.Clause n) → ℝ) :
    (∫ F, f F ∂Measure.pi (fun _ => ClauseEndpoint.clauseLaw n)) = uniformAverage f := by
  rw [clauseLaw_eq, pi_law, integral_law]

end SatUpper.FiniteUniformLaw
