import SatUpper.PoissonFunctional

/-! Replica moments with independent fresh factors. Repeated replica states
evaluate the same fresh sample; no independence between repeated labels is assumed. -/

open MeasureTheory

namespace SatUpper.ReplicaMoments

variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]

theorem integrable_unit_interval (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : Measurable f) (h0 : ∀ x, 0 ≤ f x) (h1 : ∀ x, f x ≤ 1) :
    Integrable f μ := by
  apply (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (h0 x)]
    exact h1 x)

noncomputable def replicaAverage (ν : Measure Ξ) (r : ℕ) (f : Ξ → Ω → ℝ)
    (v : Fin r → Ω) : ℝ := ∫ x, ∏ h, f x (v h) ∂ν

theorem measurable_replicaAverage (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (r : ℕ) {f : Ξ → Ω → ℝ} (hf : Measurable (Function.uncurry f)) :
    Measurable (replicaAverage ν r f) := by
  have h : Measurable (fun z : Ξ × (Fin r → Ω) => ∏ j, f z.1 (z.2 j)) := by
    apply Finset.measurable_prod
    intro j _
    exact hf.comp (measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd))
  exact h.stronglyMeasurable.integral_prod_left.measurable

theorem replicaAverage_bounds (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (r : ℕ) {f : Ξ → Ω → ℝ} (hf : Measurable (Function.uncurry f))
    (h0 : ∀ x ω, 0 ≤ f x ω) (h1 : ∀ x ω, f x ω ≤ 1) (v : Fin r → Ω) :
    0 ≤ replicaAverage ν r f v ∧ replicaAverage ν r f v ≤ 1 := by
  have hm : Measurable (fun x => ∏ j, f x (v j)) := by
    apply Finset.measurable_prod
    intro j _
    exact hf.comp (measurable_id.prodMk measurable_const)
  have hp0 (x) : 0 ≤ ∏ j, f x (v j) := Finset.prod_nonneg (fun j _ => h0 x (v j))
  have hp1 (x) : (∏ j, f x (v j)) ≤ 1 :=
    Finset.prod_le_one (fun j _ => h0 x (v j)) (fun j _ => h1 x (v j))
  constructor
  · exact integral_nonneg hp0
  · have h := integral_mono (integrable_unit_interval ν hm hp0 hp1)
      (integrable_const (1 : ℝ)) hp1
    simpa only [replicaAverage, integral_const, measureReal_univ_eq_one, one_smul] using h

noncomputable def productMoment (ν : Measure Ξ) (μ : Measure Ω) (k r : ℕ)
    (f : Fin k → Ξ → Ω → ℝ) : ℝ :=
  ∫ x : Fin k → Ξ, (∫ ω, ∏ j, f j (x j) ω ∂μ)^r ∂Measure.pi (fun _ => ν)

theorem productMoment_eq_replicas (ν : Measure Ξ) (μ : Measure Ω)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure μ] (k r : ℕ)
    {f : Fin k → Ξ → Ω → ℝ} (hf : ∀ j, Measurable (Function.uncurry (f j)))
    (h0 : ∀ j x ω, 0 ≤ f j x ω) (h1 : ∀ j x ω, f j x ω ≤ 1) :
    productMoment ν μ k r f =
      ∫ v : Fin r → Ω, ∏ j, replicaAverage ν r (f j) v ∂Measure.pi (fun _ => μ) := by
  have hmeas : Measurable (fun z : (Fin k → Ξ) × (Fin r → Ω) =>
      ∏ h, ∏ j, f j (z.1 j) (z.2 h)) := by
    apply Finset.measurable_prod
    intro h _
    apply Finset.measurable_prod
    intro j _
    have he : Measurable (fun z : (Fin k → Ξ) × (Fin r → Ω) => (z.1 j, z.2 h)) :=
      ((measurable_pi_apply j).comp measurable_fst).prodMk
        ((measurable_pi_apply h).comp measurable_snd)
    exact (hf j).comp he
  have hp0 (z : (Fin k → Ξ) × (Fin r → Ω)) :
      0 ≤ ∏ h, ∏ j, f j (z.1 j) (z.2 h) :=
    Finset.prod_nonneg (fun h _ => Finset.prod_nonneg (fun j _ => h0 j _ _))
  have hp1 (z : (Fin k → Ξ) × (Fin r → Ω)) :
      (∏ h, ∏ j, f j (z.1 j) (z.2 h)) ≤ 1 :=
    Finset.prod_le_one
      (fun h _ => Finset.prod_nonneg (fun j _ => h0 j _ _))
      (fun h _ => Finset.prod_le_one (fun j _ => h0 j _ _) (fun j _ => h1 j _ _))
  have hi := integrable_unit_interval
    ((Measure.pi (fun _ : Fin k => ν)).prod (Measure.pi (fun _ : Fin r => μ))) hmeas hp0 hp1
  have hpow (x : Fin k → Ξ) :
      (∫ ω, ∏ j, f j (x j) ω ∂μ)^r =
        ∫ v : Fin r → Ω, ∏ h, ∏ j, f j (x j) (v h) ∂Measure.pi (fun _ => μ) := by
    simpa only [Fintype.card_fin] using
      (integral_fintype_prod_eq_pow (ι := Fin r) (μ := μ) (fun ω => ∏ j, f j (x j) ω)).symm
  unfold productMoment
  simp_rw [hpow]
  rw [integral_integral_swap hi]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro v
  dsimp only
  have he : (fun x : Fin k → Ξ => ∏ h, ∏ j, f j (x j) (v h)) =
      (fun x : Fin k → Ξ => ∏ j, ∏ h, f j (x j) (v h)) := by
    funext x
    exact Finset.prod_comm
  rw [he]
  exact integral_fintype_prod_eq_prod (fun j x => ∏ h, f j x (v h))

end SatUpper.ReplicaMoments
