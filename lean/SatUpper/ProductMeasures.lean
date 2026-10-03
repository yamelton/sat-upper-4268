import Mathlib.MeasureTheory.Constructions.Pi

open MeasureTheory

namespace SatUpper.ProductMeasures

/-- Currying independent coordinates preserves their product law, including
when the row index types and coordinate laws depend on the row. -/
theorem piCurry {I : Type*} {J : I → Type*} {B : (i : I) → J i → Type*}
    [Fintype I] [∀ i, Fintype (J i)] [∀ i j, MeasurableSpace (B i j)]
    (μ : ∀ i j, Measure (B i j)) [∀ i j, SigmaFinite (μ i j)] :
    MeasurePreserving (MeasurableEquiv.piCurry B)
      (Measure.pi (fun p : Sigma J => μ p.1 p.2))
      (Measure.pi (fun i => Measure.pi (μ i))) := by
  apply MeasurePreserving.symm (MeasurableEquiv.piCurry B).symm
  refine ⟨(MeasurableEquiv.piCurry B).symm.measurable, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi hs)]
  have he : (MeasurableEquiv.piCurry B).symm ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun i => Set.univ.pi (fun j => s ⟨i,j⟩)) := by
    ext x
    simp [Set.mem_pi, Sigma.forall, Sigma.uncurry]
  rw [he, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  exact (Fintype.prod_sigma (fun p : Sigma J => μ p.1 p.2 (s p))).symm

theorem uncurry {I J B : Type*} [Fintype I] [Fintype J] [MeasurableSpace B]
    (μ : I → J → Measure B) [∀ i j, SigmaFinite (μ i j)] :
    Measure.map (fun a : I → J → B => fun p : I × J => a p.1 p.2)
      (Measure.pi (fun i => Measure.pi (μ i))) =
      Measure.pi (fun p : I × J => μ p.1 p.2) := by
  have h := (measurePreserving_piCongrLeft (fun p : I × J => μ p.1 p.2)
    (Equiv.sigmaEquivProd I J)).comp
    (MeasurePreserving.symm (MeasurableEquiv.piCurry (fun (_ : I) (_ : J) => B)) (piCurry μ))
  exact h.map_eq

end SatUpper.ProductMeasures
