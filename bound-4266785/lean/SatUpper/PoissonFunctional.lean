import SatUpper.PoissonConfiguration
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic.Ring

/-! The probability generating functional of the constructed finite Poisson
configuration. All expectations here refer to the actual constructed measure. -/

open MeasureTheory ProbabilityTheory
open SatUpper.PoissonConfiguration
open scoped ENNReal NNReal

namespace SatUpper.PoissonFunctional

variable {α : Type*} [MeasurableSpace α]

noncomputable def productTest (f : α → ℝ) (x : Configuration α) : ℝ := ∏ i, f (x.2 i)

theorem measurable_productTest {f : α → ℝ} (hf : Measurable f) :
    Measurable (productTest f) := by
  apply measurable_fromConfiguration
  intro n
  exact Finset.measurable_prod Finset.univ (fun i _ => hf.comp (measurable_pi_apply i))

omit [MeasurableSpace α] in
theorem productTest_bounds {f : α → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (x : Configuration α) : 0 ≤ productTest f x ∧ productTest f x ≤ 1 := by
  constructor
  · exact Finset.prod_nonneg (fun i _ => hf0 (x.2 i))
  · exact Finset.prod_le_one (fun i _ => hf0 (x.2 i)) (fun i _ => hf1 (x.2 i))

theorem integrable_productTest {f : α → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (μ : Measure (Configuration α)) [IsFiniteMeasure μ] :
    Integrable (productTest f) μ := by
  apply (integrable_const (1 : ℝ)).mono' (measurable_productTest hf).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (productTest_bounds hf0 hf1 x).1]
  exact (productTest_bounds hf0 hf1 x).2

theorem integral_fixedSize_product (n : ℕ) (ν : Measure α) [IsProbabilityMeasure ν]
    {f : α → ℝ} (hf : Measurable f) :
    (∫ x, productTest f x ∂fixedSize n ν) = (∫ x, f x ∂ν) ^ n := by
  rw [fixedSize, integral_map (measurable_mk n).aemeasurable
    (measurable_productTest hf).aestronglyMeasurable]
  change (∫ x : Fin n → α, ∏ i, f (x i) ∂Measure.pi (fun _ : Fin n => ν)) = _
  simpa using (integral_fintype_prod_eq_pow (ι := Fin n) (μ := ν) f)

/-- The scalar Poisson generating series, proved from the exponential series. -/
theorem poisson_generating_series (r : ℝ≥0) (t : ℝ) :
    HasSum (fun n => poissonPMFReal r n * t ^ n) (Real.exp (r * (t - 1))) := by
  have he : HasSum (fun n : ℕ => ((r : ℝ) * t) ^ n / n.factorial)
      (Real.exp ((r : ℝ) * t)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp ℝ _
  have h := he.mul_left (Real.exp (-(r : ℝ)))
  have hterm : (fun n => poissonPMFReal r n * t ^ n) =
      (fun n : ℕ => Real.exp (-(r : ℝ)) * (((r : ℝ) * t) ^ n / n.factorial)) := by
    funext n
    rw [poissonPMFReal, mul_pow]
    ring
  have hexp : Real.exp (-(r : ℝ)) * Real.exp ((r : ℝ) * t) =
      Real.exp ((r : ℝ) * (t - 1)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hterm, ← hexp]
  exact h

/-- Generating functional for arbitrary measurable tests in `[0,1]`. -/
theorem integral_poisson_product (r : ℝ≥0) (ν : Measure α) [IsProbabilityMeasure ν]
    {f : α → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    (∫ x, productTest f x ∂poisson r ν) = Real.exp ((r : ℝ) * ((∫ x, f x ∂ν) - 1)) := by
  have hint := integrable_productTest hf hf0 hf1 (poisson r ν)
  unfold poisson randomSize at hint ⊢
  rw [integral_sum_measure hint]
  simp_rw [integral_smul_measure, integral_fixedSize_product _ ν hf, smul_eq_mul]
  have hreal : ∀ n, (poissonPMF r n).toReal = poissonPMFReal r n := by
    intro n
    exact ENNReal.toReal_ofReal poissonPMFReal_nonneg
  simp_rw [hreal]
  exact (poisson_generating_series r (∫ x, f x ∂ν)).tsum_eq

end SatUpper.PoissonFunctional
