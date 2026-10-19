import SatKUpper.SiteProducts
import SatKUpper.MeanComparison
import SatUpper.PoissonMixture

/-! Bound the site entropy by a finite polynomial, then evaluate its
Poisson expectation. -/

open MeasureTheory ProbabilityTheory SatUpper SatKUpper.Sampling SatKUpper.Ground SatKUpper.SiteProducts
open SatUpper.PoissonConfiguration SatKUpper.SiteVertex
open scoped NNReal

namespace SatKUpper.SiteBound

variable {t r n L : ℕ} (law : CoinLaw t)

theorem product_surveys (s : Fin L → Fresh t r n) (v : Fin n) (b : Bool) :
    (∏ i, mark law (SiteGround.surveys s v b i)) =
      side law (v,b) ⟨L,s⟩ := by
  unfold side PoissonFunctional.productTest test
  rw [← Finset.prod_filter]
  symm
  exact Finset.prod_subtype _ (by simp [Prod.ext_iff]) _

theorem entropy_le {y : ℝ} (hy : 0 ≤ y)
    (s : Fin L → Fresh t r n) (K : ℕ) :
    entropy law y Fin.elim0 s ≤ ∑ v : Fin n, upper law K (Real.exp (-y)) v ⟨L,s⟩ := by
  have he := SiteGround.entropy_le law hy s
  change entropy law y Fin.elim0 s ≤ _ at he
  simp_rw [SiteVertex.vertex_moment, product_surveys] at he
  refine he.trans (Finset.sum_le_sum (fun v _ => ?_))
  exact PoissonPair.log_majorant (side_bounds law (v,true) ⟨L,s⟩).1
    (side_bounds law (v,true) ⟨L,s⟩).2 (side_bounds law (v,false) ⟨L,s⟩).1
    (side_bounds law (v,false) ⟨L,s⟩).2 (Real.exp_pos (-y))
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hy)) K

noncomputable def configEntropy (y : ℝ) (c : Configuration (Fresh t r n)) : ℝ :=
  entropy law y Fin.elim0 c.2

theorem measurable_configEntropy (n : ℕ) (y : ℝ) :
    Measurable (configEntropy (r := r) (n := n) law y) :=
  measurable_fromConfiguration (fun _ => measurable_of_countable _)

theorem integrable_entropy [NeZero n] {y : ℝ} (hy : 0 ≤ y)
    (q : ℝ≥0) : Integrable (configEntropy (r := r) (n := n) law y) (poisson q (freshLaw law r n)) := by
  apply ((CompoundPoissonMoments.integrable_size q (freshLaw law r n)).const_mul y).mono'
    (measurable_configEntropy (r := r) law n y).aestronglyMeasurable
  filter_upwards [] with c
  have h := Ground.entropy_bounds law hy (Fin.elim0 : Fin 0 → Fresh t r n) c.2
  simp only [Nat.cast_zero, zero_add] at h
  change ‖Ground.entropy law y Fin.elim0 c.2‖ ≤ y*c.1
  rw [Real.norm_eq_abs, abs_of_nonpos h.2]
  change -entropy law y Fin.elim0 c.2 ≤ y*c.1
  linarith [h.1]

theorem fixed_mean [NeZero n] (y : ℝ) (L : ℕ) :
    MeanComparison.mean law r n y 0 L =
      ∫ s : Fin L → Fresh t r n, configEntropy law y ⟨L,s⟩ ∂Measure.pi (fun _ => freshLaw law r n) := by
  have he (c : Fin 0 → Fresh t r n) : c = Fin.elim0 := Subsingleton.elim _ _
  simp only [MeanComparison.mean, he, integral_const, measureReal_univ_eq_one, one_smul, configEntropy]

theorem endpoint [NeZero n] {y : ℝ} (hy : 0 ≤ y) (q : ℝ≥0) (K : ℕ) :
    DirectPoisson.expectation (MeanComparison.mean law r n y) 0 q ≤
      n*(-(∑ h ∈ Finset.range K,
        (complementMoment law r ((q : ℝ)/(2*n)) (h+1))^2/(h+1)) +
        K * Real.exp (-y)) := by
  have hc := DirectPoisson.integrable_row
    (MeanComparison.site_difference_bound law (r := r) (n := n) hy) q 0
  change Integrable (fun L => MeanComparison.mean law r n y 0 L) (poissonMeasure q) at hc
  simp_rw [fixed_mean] at hc
  rw [DirectPoisson.expectation, DirectPoisson.zero_law, integral_dirac]
  simp_rw [fixed_mean]
  rw [← PoissonMixture.integral_eq_count_integral q (freshLaw law r n)
    (measurable_configEntropy (r := r) law n y) (integrable_entropy (r := r) (n := n) law hy q) hc]
  have hs := integrable_finset_sum Finset.univ
    (fun (v : Fin n) _ => integrable_upper (r := r) law q K (Real.exp (-y)) v)
  have h := integral_mono (integrable_entropy (r := r) (n := n) law hy q) hs
    (fun c => entropy_le law hy c.2 K)
  rw [integral_finset_sum _ (fun v _ => integrable_upper (r := r) law q K (Real.exp (-y)) v)] at h
  simp only [integral_upper, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  exact h

end SatKUpper.SiteBound
