import SatUpper.PoissonExpectation

/-! Integrating a Poisson configuration by conditioning on its count. -/

open MeasureTheory ProbabilityTheory
open SatUpper.PoissonConfiguration
open scoped ENNReal NNReal

namespace SatUpper.PoissonMixture

variable {α : Type*} [MeasurableSpace α]

theorem integral_eq_count_integral (r : ℝ≥0) (ν : Measure α) [IsProbabilityMeasure ν]
    {f : Configuration α → ℝ} (hf : Measurable f)
    (hi : Integrable f (poisson r ν))
    (hcount : Integrable (fun K => ∫ a, f ⟨K,a⟩ ∂Measure.pi (fun _ : Fin K => ν)) (poissonMeasure r)) :
    (∫ c, f c ∂poisson r ν) =
      ∫ K, ∫ a, f ⟨K,a⟩ ∂Measure.pi (fun _ : Fin K => ν) ∂poissonMeasure r := by
  unfold poisson randomSize at hi ⊢
  rw [integral_sum_measure hi, integral_countable' hcount]
  apply tsum_congr
  intro K
  rw [integral_smul_measure, fixedSize,
    integral_map (measurable_mk K).aemeasurable hf.aestronglyMeasurable]
  have he : (poissonMeasure r).real {K} = (poissonPMF r K).toReal := by
    have h : poissonMeasure r {K} = poissonPMF r K :=
      PMF.toMeasure_apply_singleton (poissonPMF r) K (measurableSet_singleton K)
    exact congrArg ENNReal.toReal h
  rw [he]

end SatUpper.PoissonMixture
