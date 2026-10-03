import SatUpper.Direct.Finite
import SatUpper.ProductMeasures
import Mathlib.MeasureTheory.Integral.Prod

/-! Splitting a finite product at its first coordinate, with distinct laws. -/

open MeasureTheory
open scoped ENNReal

namespace SatUpper.DirectProduct

variable {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]

theorem integral_cons {L : ℕ} (ν : Measure A) (μ : Fin L → Measure A)
    [IsProbabilityMeasure ν] [∀ i, IsProbabilityMeasure (μ i)]
    (f : (Fin (L+1) → A) → ℝ) :
    (∫ a, f a ∂Measure.pi (Fin.cons ν μ)) =
      ∫ a, ∫ v, f (Fin.cons v a) ∂ν ∂Measure.pi μ := by
  letI : ∀ i : Fin (L+1), IsProbabilityMeasure ((Fin.cons ν μ : Fin (L+1) → Measure A) i) := by
    intro i
    cases i using Fin.cases with
    | zero => change IsProbabilityMeasure ν; infer_instance
    | succ i => change IsProbabilityMeasure (μ i); infer_instance
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (L+1) => A) 0
  have h := (measurePreserving_piFinSuccAbove (Fin.cons ν μ) 0).symm e
  have he : (fun z : A × (Fin L → A) => (Fin.cons z.1 z.2 : Fin (L+1) → A)) = e.symm := by
    funext z j
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  have hi := h.integral_comp e.symm.measurableEmbedding f
  simp only [Fin.cons_zero, Fin.succAbove_zero, Fin.cons_succ, ← he] at hi
  rw [← hi, integral_prod _ Integrable.of_finite]
  exact integral_integral_swap Integrable.of_finite

theorem integral_iid_cons (ν : Measure A) [IsProbabilityMeasure ν] (L : ℕ)
    (f : (Fin (L+1) → A) → ℝ) :
    (∫ a, f a ∂Measure.pi (fun _ => ν)) =
      ∫ a, ∫ v, f (Fin.cons v a) ∂ν ∂Measure.pi (fun _ => ν) := by
  have he : (Fin.cons ν (fun _ : Fin L => ν) : Fin (L+1) → Measure A) = fun _ => ν := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  rw [← he, integral_cons]

theorem uniform_eq_count (A : Type*) [Fintype A] [Nonempty A] [MeasurableSpace A]
    [MeasurableSingletonClass A] :
    DirectFinite.uniform A = (Fintype.card A : ℝ≥0∞)⁻¹ • Measure.count := by
  apply Measure.ext_of_singleton
  intro a
  rw [DirectFinite.uniform, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a),
    PMF.uniformOfFintype_apply]
  simp [Measure.smul_apply, smul_eq_mul]

theorem triple_law {B : Type*} [MeasurableSpace B] (μ : Fin 3 → Measure B)
    [∀ j, IsProbabilityMeasure (μ j)] :
    Measure.map (fun v : Fin 3 → B => (v 0,v 1,v 2)) (Measure.pi μ) =
      (μ 0).prod ((μ 1).prod (μ 2)) := by
  have h1 := measurePreserving_piFinSuccAbove μ 0
  have h2 := measurePreserving_piFinTwo (fun j : Fin 2 => μ j.succ)
  have hid : MeasurePreserving (id : B → B) (μ 0) (μ 0) := ⟨measurable_id, Measure.map_id⟩
  exact ((hid.prod h2).comp h1).map_eq

end SatUpper.DirectProduct
