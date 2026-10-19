import SatKUpper.BetaMoments

/-! Realize the beta distribution on the [0,1) coin space. -/

open MeasureTheory ProbabilityTheory SatKUpper.FiniteApproximation

namespace SatKUpper.BetaCoin

noncomputable def project (x : ℝ) : Coin :=
  ⟨if 0 ≤ x ∧ x < 1 then x else 0, by split <;> simp_all⟩

theorem measurable_project : Measurable project :=
  (Measurable.ite measurableSet_Ico measurable_id measurable_const).subtype_mk

theorem project_eq {x : ℝ} (hx : 0 ≤ x ∧ x < 1) : (project x).val = x := by
  simp [project, hx]

noncomputable def base (a b : ℝ) : Measure Coin := Measure.map project (betaMeasure a b)

theorem base_probability {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IsProbabilityMeasure (base a b) := by
  letI := isProbabilityMeasureBeta ha hb
  exact Measure.isProbabilityMeasure_map measurable_project.aemeasurable

theorem integral_pow {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : ℕ) :
    (∫ x : Coin, x.val^h ∂base a b) = BetaMoments.u a b h := by
  rw [base, integral_map measurable_project.aemeasurable
    (measurable_subtype_coe.pow_const h).aestronglyMeasurable]
  rw [← BetaMoments.integral_pow ha hb h]
  apply integral_congr_ae
  filter_upwards [BetaMoments.ae_support a b] with x hx
  rw [project_eq ⟨hx.1.le,hx.2⟩]

theorem integrable_pow (μ : Measure Coin) [IsProbabilityMeasure μ] (h : ℕ) :
    Integrable (fun x : Coin => x.val^h) μ :=
  SatUpper.ReplicaMoments.integrable_unit_interval μ (measurable_subtype_coe.pow_const h)
    (fun x => pow_nonneg x.property.1 h)
    (fun x => pow_le_one₀ x.property.1 x.property.2.le)

end SatKUpper.BetaCoin
