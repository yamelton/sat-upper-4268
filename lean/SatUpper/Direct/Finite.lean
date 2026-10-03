import SatUpper.TrialFields
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-! Finite sampling laws. A seed records a signed variable
and a survey. Each row then samples three independent Boolean warnings. -/

open MeasureTheory
open scoped ENNReal

namespace SatUpper.DirectFinite

abbrev Spin (n : ℕ) := Fin n → Bool
abbrev Seed (n : ℕ) := (Fin n × Bool) × Fin 4
abbrev Fresh (n : ℕ) := Fin 3 → Seed n
abbrev Fields (L : ℕ) := Fin L → Fin 3 → Bool

noncomputable def uniform (A : Type*) [Fintype A] [Nonempty A] [MeasurableSpace A] : Measure A :=
  (PMF.uniformOfFintype A).toMeasure

instance (A : Type*) [Fintype A] [Nonempty A] [MeasurableSpace A] :
    IsProbabilityMeasure (uniform A) := by unfold uniform; infer_instance

theorem integral_uniform {A : Type*} [Fintype A] [Nonempty A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (f : A → ℝ) :
    (∫ a, f a ∂uniform A) = (∑ a, f a) / Fintype.card A := by
  rw [uniform, PMF.integral_eq_tsum _ _ Integrable.of_finite, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    smul_eq_mul, ← Finset.mul_sum, div_eq_mul_inv]
  ring

noncomputable def seedLaw (n : ℕ) [NeZero n] : Measure (Seed n) :=
  (uniform (Fin n × Bool)).prod (uniform (Fin 4))

instance (n : ℕ) [NeZero n] : IsProbabilityMeasure (seedLaw n) := by unfold seedLaw; infer_instance

noncomputable def freshLaw (n : ℕ) [NeZero n] : Measure (Fresh n) :=
  Measure.pi (fun _ => seedLaw n)

instance (n : ℕ) [NeZero n] : IsProbabilityMeasure (freshLaw n) := by unfold freshLaw; infer_instance

noncomputable def innerLaw {n : ℕ} (x : Seed n) : Measure Bool := TrialFields.stateLaw x.2

instance {n : ℕ} (x : Seed n) : IsProbabilityMeasure (innerLaw x) := by unfold innerLaw; infer_instance

noncomputable def rowLaw {n : ℕ} (x : Fresh n) : Measure (Fin 3 → Bool) :=
  Measure.pi (fun j => innerLaw (x j))

instance {n : ℕ} (x : Fresh n) : IsProbabilityMeasure (rowLaw x) := by unfold rowLaw; infer_instance

noncomputable def fieldLaw {n L : ℕ} (s : Fin L → Fresh n) : Measure (Fields L) :=
  Measure.pi (fun i => rowLaw (s i))

instance {n L : ℕ} (s : Fin L → Fresh n) : IsProbabilityMeasure (fieldLaw s) := by
  unfold fieldLaw
  infer_instance

end SatUpper.DirectFinite
