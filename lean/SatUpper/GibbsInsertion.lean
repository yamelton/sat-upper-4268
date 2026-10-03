import SatUpper.ReplicaMoments
import Mathlib.MeasureTheory.Measure.Tilted

/-! A partition ratio is a Gibbs expectation. -/

open MeasureTheory

namespace SatUpper.GibbsInsertion

variable {Ω : Type*} [MeasurableSpace Ω]

theorem partition_ratio (μ : Measure Ω) [IsProbabilityMeasure μ]
    {H Z : Ω → ℝ} (hH : Integrable (fun ω => Real.exp (H ω)) μ)
    (hZ : Measurable Z) (h0 : ∀ ω, 0 ≤ Z ω) (h1 : ∀ ω, Z ω ≤ 1)
    (q : ℝ) :
    (∫ ω, Real.exp (H ω)*(1-q*Z ω) ∂μ) / (∫ ω, Real.exp (H ω) ∂μ) =
      1-q*(∫ ω, Z ω ∂μ.tilted H) := by
  letI := isProbabilityMeasure_tilted hH
  have hiZ := ReplicaMoments.integrable_unit_interval (μ.tilted H) hZ h0 h1
  have hiW : Integrable (fun ω => Real.exp (H ω)*Z ω) μ := by
    simpa only [smul_eq_mul] using (integrable_tilted_iff hH Z).mp hiZ
  have hp : 0 < ∫ ω, Real.exp (H ω) ∂μ := integral_exp_pos hH
  rw [integral_tilted]
  simp only [smul_eq_mul]
  have he : (fun ω => Real.exp (H ω)*(1-q*Z ω)) =
      (fun ω => Real.exp (H ω)-q*(Real.exp (H ω)*Z ω)) := by funext ω; ring
  rw [he, integral_sub hH (hiW.const_mul q), integral_const_mul]
  have he' : (fun ω => (Real.exp (H ω)/(∫ ω, Real.exp (H ω) ∂μ))*Z ω) =
      (fun ω => (Real.exp (H ω)*Z ω)/(∫ ω, Real.exp (H ω) ∂μ)) := by funext ω; ring
  rw [he', integral_div]
  field_simp

end SatUpper.GibbsInsertion
