import SatUpper.SiteVertexIdentity
import SatUpper.ProductMeasures
import Mathlib.Probability.Independence.InfinitePi

/-! Selecting distinct coordinates preserves their possibly different finite laws. -/

open MeasureTheory ProbabilityTheory

namespace SatUpper.FiniteCoordinateSelection

variable {I J B : Type*} [Fintype I] [Fintype J] [MeasurableSpace B]

theorem select_law (μ : J → Measure B) [∀ j, IsProbabilityMeasure (μ j)]
    (f : I → J) (hf : Function.Injective f) :
    Measure.map (fun a : J → B => fun i => a (f i)) (Measure.pi μ) =
      Measure.pi (fun i => μ (f i)) := by
  have h := iIndepFun_infinitePi (μ := μ) (X := fun _ => (id : B → B))
    (fun _ => measurable_id)
  have hi := iIndepFun.precomp hf h
  have he := (iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun i => measurable_pi_apply (f i))).mp hi
  have heval (j : J) : Measure.map (fun a : J → B => a j) (Measure.pi μ) = μ j :=
    (measurePreserving_eval μ j).map_eq
  simp only [heval, Measure.infinitePi_eq_pi] at he
  exact he

theorem flatten_law (μ : I → Fin 2 → Measure B) [∀ i j, IsProbabilityMeasure (μ i j)] :
    Measure.map (fun a : I → Fin 2 → B => fun p : I × Fin 2 => a p.1 p.2)
      (Measure.pi (fun i => Measure.pi (μ i))) =
      Measure.pi (fun p : I × Fin 2 => μ p.1 p.2) :=
  ProductMeasures.uncurry μ

theorem pair_law (μ : I → Fin 2 → Measure B) [∀ i j, IsProbabilityMeasure (μ i j)] :
    Measure.map (fun a : I × Fin 2 → B => fun i => (a (i,0),a (i,1)))
      (Measure.pi (fun p : I × Fin 2 => μ p.1 p.2)) =
      Measure.pi (fun i => (μ i 0).prod (μ i 1)) := by
  rw [← flatten_law μ, Measure.map_map (by fun_prop) (by fun_prop)]
  have h := Measure.pi_map_pi (μ := fun i => Measure.pi (μ i))
    (f := fun _ => fun x : Fin 2 → B => (x 0,x 1)) (fun _ => by fun_prop)
  have hpair (i : I) : Measure.map (fun x : Fin 2 → B => (x 0,x 1))
      (Measure.pi (μ i)) = (μ i 0).prod (μ i 1) :=
    (measurePreserving_piFinTwo (μ i)).map_eq
  simp only [hpair] at h
  exact h

end SatUpper.FiniteCoordinateSelection
