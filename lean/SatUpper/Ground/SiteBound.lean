import SatUpper.Direct.SiteProducts
import SatUpper.Ground.Site
import SatUpper.PoissonMixture

/-! Bound the site entropy by a finite polynomial, then evaluate its
Poisson expectation. -/

open MeasureTheory ProbabilityTheory SatUpper.DirectFinite SatUpper.GroundFinite SatUpper.DirectSiteProducts
open SatUpper.PoissonConfiguration SatUpper.WitnessVertex
open scoped NNReal

namespace SatUpper.GroundSiteBound

theorem product_surveys {n L : ℕ} (s : Fin L → Fresh n) (v : Fin n) (b : Bool) :
    (∏ i, mark (SiteSideLaw.surveys (fun i j => (s i j).1) v b (fun p => (s p.1 p.2).2) i)) =
      side (v,b) ⟨L,s⟩ := by
  unfold side PoissonFunctional.productTest test
  rw [← Finset.prod_filter]
  symm
  exact Finset.prod_subtype _ (by simp [Prod.ext_iff]) _

theorem entropy_le {n L : ℕ} {y : ℝ} (hy : 0 ≤ y)
    (s : Fin L → Fresh n) (K : ℕ) :
    entropy y Fin.elim0 s ≤ ∑ v : Fin n, upper K (Real.exp (-y)) v ⟨L,s⟩ := by
  have he := GroundSite.entropy_le hy (fun i j => (s i j).1) (fun p => (s p.1 p.2).2)
  change entropy y Fin.elim0 s ≤ _ at he
  simp_rw [GroundSite.vertex_moment, product_surveys] at he
  refine he.trans (Finset.sum_le_sum (fun v _ => ?_))
  exact PoissonPair.log_majorant (side_bounds (v,true) ⟨L,s⟩).1
    (side_bounds (v,true) ⟨L,s⟩).2 (side_bounds (v,false) ⟨L,s⟩).1
    (side_bounds (v,false) ⟨L,s⟩).2 (Real.exp_pos (-y))
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hy)) K

noncomputable def configEntropy {n : ℕ} (y : ℝ) (c : Configuration (Fresh n)) : ℝ :=
  entropy y Fin.elim0 c.2

theorem measurable_configEntropy (n : ℕ) (y : ℝ) :
    Measurable (configEntropy (n := n) y) :=
  measurable_fromConfiguration (fun _ => measurable_of_countable _)

theorem integrable_entropy {n : ℕ} [NeZero n] {y : ℝ} (hy : 0 ≤ y)
    (r : ℝ≥0) : Integrable (configEntropy (n := n) y) (poisson r (freshLaw n)) := by
  apply ((CompoundPoissonMoments.integrable_size r (freshLaw n)).const_mul y).mono'
    (measurable_configEntropy n y).aestronglyMeasurable
  filter_upwards [] with c
  have h := GroundFinite.entropy_bounds hy (Fin.elim0 : Fin 0 → Fresh n) c.2
  simp only [Nat.cast_zero, zero_add] at h
  change ‖GroundFinite.entropy y Fin.elim0 c.2‖ ≤ y*c.1
  rw [Real.norm_eq_abs, abs_of_nonpos h.2]
  change -entropy y Fin.elim0 c.2 ≤ y*c.1
  linarith [h.1]

theorem fixed_mean {n : ℕ} [NeZero n] (y : ℝ) (L : ℕ) :
    GroundComparison.mean n y 0 L =
      ∫ s : Fin L → Fresh n, configEntropy y ⟨L,s⟩ ∂Measure.pi (fun _ => freshLaw n) := by
  have he (c : Fin 0 → Fresh n) : c = Fin.elim0 := Subsingleton.elim _ _
  simp only [GroundComparison.mean, he, integral_const, measureReal_univ_eq_one, one_smul, configEntropy]

theorem endpoint {n : ℕ} [NeZero n] {y : ℝ} (hy : 0 ≤ y)
    (r : ℝ≥0) (hr : (r : ℝ)/(2*n) = 3*(Witness.alpha : ℝ)/2) (K : ℕ) :
    DirectPoisson.expectation (GroundComparison.mean n y) 0 r ≤
      n*(negativeMomentSum K Formalization.noWarningMoment +
        K * Real.exp (-y)) := by
  have hc := DirectPoisson.integrable_row (GroundComparison.site_difference_bound (n := n) hy) r 0
  change Integrable (fun L => GroundComparison.mean n y 0 L) (poissonMeasure r) at hc
  simp_rw [fixed_mean] at hc
  rw [DirectPoisson.expectation, DirectPoisson.zero_law, integral_dirac]
  simp_rw [fixed_mean]
  rw [← PoissonMixture.integral_eq_count_integral r (freshLaw n)
    (measurable_configEntropy n y) (integrable_entropy (n := n) hy r) hc]
  have hs := integrable_finset_sum Finset.univ (fun (v : Fin n) _ => integrable_upper r K (Real.exp (-y)) v)
  have h := integral_mono (integrable_entropy (n := n) hy r)
    hs
    (fun c => entropy_le hy c.2 K)
  rw [integral_finset_sum _ (fun v _ => integrable_upper r K (Real.exp (-y)) v)] at h
  simp only [integral_upper r hr, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  exact h

end SatUpper.GroundSiteBound
