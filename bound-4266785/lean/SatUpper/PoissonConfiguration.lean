import Mathlib.Probability.Distributions.Poisson
import Mathlib.MeasureTheory.Constructions.Pi

/-!
Finite random configurations: a random size followed by independent locations.
The size distribution is a PMF, specialized below to Poisson. Ordered atoms
retain multiplicities; no quotient or simplicity assumption is needed.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace SatUpper.PoissonConfiguration

abbrev Configuration (α : Type*) := Σ n : ℕ, Fin n → α

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

theorem measurable_mk (n : ℕ) : Measurable (@Sigma.mk ℕ (fun n => Fin n → α) n) :=
  Measurable.of_le_map (iInf_le _ n)

theorem measurable_fromConfiguration {f : Configuration α → β}
    (hf : ∀ n, Measurable (f ∘ Sigma.mk n)) : Measurable f :=
  Measurable.of_comap_le (le_iInf fun n => MeasurableSpace.comap_le_iff_le_map.mpr (hf n))

noncomputable def fixedSize (n : ℕ) (ν : Measure α) : Measure (Configuration α) :=
  Measure.map (Sigma.mk n) (Measure.pi (fun _ : Fin n => ν))

noncomputable def randomSize (p : PMF ℕ) (ν : Measure α) : Measure (Configuration α) :=
  Measure.sum (fun n => p n • fixedSize n ν)

noncomputable def poisson (r : ℝ≥0) (ν : Measure α) : Measure (Configuration α) :=
  randomSize (poissonPMF r) ν

theorem fixedSize_univ (n : ℕ) (ν : Measure α) [IsProbabilityMeasure ν] :
    fixedSize n ν Set.univ = 1 := by
  simp [fixedSize, Measure.map_apply (measurable_mk n) MeasurableSet.univ]

theorem randomSize_univ (p : PMF ℕ) (ν : Measure α) [IsProbabilityMeasure ν] :
    randomSize p ν Set.univ = 1 := by
  simp only [randomSize, Measure.sum_apply _ MeasurableSet.univ,
    Measure.smul_apply, smul_eq_mul, fixedSize_univ, mul_one]
  exact p.tsum_coe

instance (p : PMF ℕ) (ν : Measure α) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (randomSize p ν) := ⟨randomSize_univ p ν⟩

instance (r : ℝ≥0) (ν : Measure α) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (poisson r ν) := by unfold poisson; infer_instance

theorem measurable_size : Measurable (Sigma.fst : Configuration α → ℕ) := by
  apply measurable_fromConfiguration
  intro n
  exact measurable_const

theorem size_fixedSize (n : ℕ) (ν : Measure α) [IsProbabilityMeasure ν] :
    Measure.map Sigma.fst (fixedSize n ν) = Measure.dirac n := by
  rw [fixedSize, Measure.map_map measurable_size (measurable_mk n)]
  change Measure.map (fun _ : Fin n → α => n) (Measure.pi (fun _ : Fin n => ν)) = _
  rw [Measure.map_const, measure_univ, one_smul]

/-- The constructed configuration really has the chosen size distribution. -/
theorem size_randomSize (p : PMF ℕ) (ν : Measure α) [IsProbabilityMeasure ν] :
    Measure.map Sigma.fst (randomSize p ν) = p.toMeasure := by
  rw [randomSize, Measure.map_sum measurable_size.aemeasurable]
  simp_rw [Measure.map_smul, size_fixedSize]
  have h := Measure.sum_smul_dirac p.toMeasure
  simpa only [PMF.toMeasure_apply_singleton p _ (measurableSet_singleton _)] using h

theorem size_poisson (r : ℝ≥0) (ν : Measure α) [IsProbabilityMeasure ν] :
    Measure.map Sigma.fst (poisson r ν) = poissonMeasure r :=
  size_randomSize (poissonPMF r) ν

end SatUpper.PoissonConfiguration
