import SatUpper.ProductMeasures

/-! Singleton masses in a finite product measure. -/

open MeasureTheory

namespace SatUpper.ConditionalArrays

variable {J : Type*} [Fintype J]

theorem pi_singleton {A : J → Type*} [∀ j, MeasurableSpace (A j)]
    (μ : ∀ j, Measure (A j)) [∀ j, SigmaFinite (μ j)] (a : ∀ j, A j) :
    Measure.pi μ {a} = ∏ j, μ j {a j} := by
  have he : ({a} : Set (∀ j, A j)) = Set.univ.pi (fun j => {a j}) := by
    ext b
    simp only [Set.mem_singleton_iff, Set.mem_pi, Set.mem_univ, forall_true_left]
    exact funext_iff
  rw [he, Measure.pi_pi]

end SatUpper.ConditionalArrays
