import SatFinal.PolynomialLog

/-! The same site argument with an arbitrary polynomial logarithm minorant. -/

open ProbabilityTheory SatUpper.PoissonFunctional
open MeasureTheory SatUpper SatKUpper SatKUpper.Sampling SatKUpper.SiteProducts
open SatUpper.PoissonConfiguration SatKUpper.SiteVertex
open scoped NNReal

namespace SatFinal.PolynomialCriterion

noncomputable def expected (P : Polynomial ℝ) (m : ℕ → ℝ) : ℝ :=
  P.sum (fun h c => c*(m h)^2)

noncomputable def site (P : Polynomial ℝ) (m : ℕ → ℝ) (r : ℕ) (α : ℝ) : ℝ :=
  -expected P (ContinuousCriterion.sideMoment m r ((r+1 : ℝ)*α/2))

section finite

variable {t r n : ℕ} (law : CoinLaw t)

noncomputable def conflict (v : Fin n) (c : Configuration (Fresh t r n)) : ℝ :=
  (1-SiteProducts.side law (v,true) c)*(1-SiteProducts.side law (v,false) c)

theorem conflict_bounds (v : Fin n) (c : Configuration (Fresh t r n)) :
    0 ≤ conflict law v c ∧ conflict law v c ≤ 1 := by
  have hA := side_bounds law (v,true) c
  have hB := side_bounds law (v,false) c
  unfold conflict
  exact ⟨mul_nonneg (by linarith) (by linarith),
    mul_le_one₀ (by linarith) (by linarith) (by linarith)⟩

variable [NeZero n]

theorem integral_conflict (q : ℝ≥0) (v : Fin n) (k : ℕ) :
    (∫ c, conflict law v c ^ k ∂poisson q (freshLaw law r n)) =
      (complementMoment law r ((q : ℝ)/(2*n)) k)^2 :=
  PoissonPair.complement_moment _ (measurable_productTest (measurable_of_countable _))
    (measurable_productTest (measurable_of_countable _))
    (fun c => (side_bounds law _ c).1) (fun c => (side_bounds law _ c).2)
    (fun c => (side_bounds law _ c).1) (fun c => (side_bounds law _ c).2)
    (poissonMoment law r ((q : ℝ)/(2*n))) (mixed_moment law q v) k

theorem integrable_polynomial (P : Polynomial ℝ) (q : ℝ≥0) (v : Fin n) :
    Integrable (fun c => P.eval (conflict law v c)) (poisson q (freshLaw law r n)) := by
  simp_rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  exact integrable_finset_sum _ (fun h _ => (integrable_complement law q v h).const_mul _)

theorem integral_polynomial (P : Polynomial ℝ) (q : ℝ≥0) (v : Fin n) :
    (∫ c, P.eval (conflict law v c) ∂poisson q (freshLaw law r n)) =
      expected P (complementMoment law r ((q : ℝ)/(2*n))) := by
  simp_rw [Polynomial.eval_eq_sum, Polynomial.sum_def, expected]
  have hi (h : ℕ) : Integrable (fun c => P.coeff h * conflict law v c ^ h)
      (poisson q (freshLaw law r n)) := (integrable_complement law q v h).const_mul _
  rw [integral_finset_sum _ (fun h _ => hi h)]
  simp_rw [integral_const_mul, integral_conflict]
  rfl

noncomputable def upper (P : Polynomial ℝ) (K : ℕ) (δ : ℝ)
    (v : Fin n) (c : Configuration (Fresh t r n)) : ℝ :=
  -P.eval (conflict law v c) + K*δ

theorem integrable_upper (P : Polynomial ℝ) (K : ℕ) (δ : ℝ)
    (q : ℝ≥0) (v : Fin n) :
    Integrable (upper law P K δ v) (poisson q (freshLaw law r n)) :=
  (integrable_polynomial (r := r) law P q v).neg.add (integrable_const _)

theorem integral_upper (P : Polynomial ℝ) (K : ℕ) (δ : ℝ)
    (q : ℝ≥0) (v : Fin n) :
    (∫ c, upper law P K δ v c ∂poisson q (freshLaw law r n)) =
      -expected P (complementMoment law r ((q : ℝ)/(2*n))) + K*δ := by
  change (∫ c, -P.eval (conflict law v c) + K*δ ∂poisson q (freshLaw law r n)) = _
  have hi := integral_add (integrable_polynomial (r := r) law P q v).neg (integrable_const (K*δ))
  simp only [Pi.neg_apply] at hi
  rw [hi, integral_neg, integral_polynomial, integral_const, measureReal_univ_eq_one, one_smul]

variable (P : Polynomial ℝ) (K : ℕ)
    (hsoft : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      Real.log (1-(1-δ)*x) ≤ -P.eval x + K*δ)

include K hsoft

omit [NeZero n] in
theorem entropy_le {L : ℕ} {y : ℝ} (hy : 0 ≤ y) (s : Fin L → Fresh t r n) :
    Ground.entropy law y Fin.elim0 s ≤ ∑ v : Fin n, upper law P K (Real.exp (-y)) v ⟨L,s⟩ := by
  have he := SiteGround.entropy_le law hy s
  change Ground.entropy law y Fin.elim0 s ≤ _ at he
  simp_rw [SiteVertex.vertex_moment, SiteBound.product_surveys] at he
  refine he.trans (Finset.sum_le_sum (fun v _ => ?_))
  have h := hsoft (conflict law v ⟨L,s⟩) (conflict_bounds law v ⟨L,s⟩)
    (Real.exp (-y)) (Real.exp_pos _) (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hy))
  convert h using 1
  congr 1
  unfold conflict noConflict
  ring

theorem endpoint {y : ℝ} (hy : 0 ≤ y) (q : ℝ≥0) :
    DirectPoisson.expectation (MeanComparison.mean law r n y) 0 q ≤
      n*(-expected P (complementMoment law r ((q : ℝ)/(2*n))) + K*Real.exp (-y)) := by
  have hc := DirectPoisson.integrable_row
    (MeanComparison.site_difference_bound law (r := r) (n := n) hy) q 0
  change Integrable (fun L => MeanComparison.mean law r n y 0 L) (poissonMeasure q) at hc
  simp_rw [SiteBound.fixed_mean] at hc
  rw [DirectPoisson.expectation, DirectPoisson.zero_law, integral_dirac]
  simp_rw [SiteBound.fixed_mean]
  rw [← PoissonMixture.integral_eq_count_integral q (freshLaw law r n)
    (SiteBound.measurable_configEntropy (r := r) law n y)
    (SiteBound.integrable_entropy (r := r) (n := n) law hy q) hc]
  have hs := integrable_finset_sum Finset.univ
    (fun (v : Fin n) _ => integrable_upper (r := r) law P K (Real.exp (-y)) q v)
  have h := integral_mono (SiteBound.integrable_entropy (r := r) (n := n) law hy q) hs
    (fun c => entropy_le law P K hsoft hy c.2)
  rw [integral_finset_sum _ (fun v _ => integrable_upper (r := r) law P K (Real.exp (-y)) q v)] at h
  simp only [integral_upper, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  exact h

theorem poisson_bound (α : ℝ≥0) {y : ℝ} (hy : 0 ≤ y) :
    (-y/n)*ClauseEndpoint.poissonMean (r+1) n (α*n) ≤
      site P (Moments.moment law) r α + (r : ℝ)*α*EdgeBound.correction law r +
        (K : ℝ)*Real.exp (-y) := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have he := ClauseEndpoint.energy_comparison (r := r) (n := n) law hy (α*n)
  have hs := endpoint (r := r) (n := n) law P K hsoft hy ((r+1)*(α*n))
  have hm : (((r+1)*(α*n) : ℝ≥0) : ℝ)/(2*n) = (r+1 : ℝ)*α/2 := by
    simp only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]
    field_simp
  rw [hm] at hs
  have hc := mul_le_mul_of_nonneg_left (EdgeBound.edge_le (r := r) (n := n) law y)
    (show 0 ≤ (r : ℝ)*(α*n : ℝ≥0) by positivity)
  have h := he.trans (sub_le_sub hs hc)
  simp only [NNReal.coe_mul, NNReal.coe_natCast] at h
  have hd := div_le_div_of_nonneg_right h hn.le
  have hf : complementMoment law r ((r+1 : ℝ)*α/2) =
      ContinuousCriterion.sideMoment (Moments.moment law) r ((r+1 : ℝ)*α/2) :=
    funext (fun h => ContinuousCriterion.finite_side law r h _)
  rw [hf] at hd
  convert hd using 1
  · ring
  · unfold site
    field_simp
    ring

omit [NeZero n] in
theorem finite_upperBound (α : ℝ≥0)
    (hneg : site P (Moments.moment law) r α + (r : ℝ)*α*EdgeBound.correction law r < 0) :
    Model.UpperBound (r+1) α := by
  apply DePoissonization.upperBound_of_poisson_bound law α K hneg
  intro n hn y hy
  letI : NeZero n := ⟨by omega⟩
  exact poisson_bound law P K hsoft α hy.le

end finite

open SatKUpper.FiniteApproximation

theorem continuous_site (P : Polynomial ℝ) (r : ℕ) (α : ℝ) :
    Continuous (fun m : ℕ → ℝ => site P m r α) := by
  unfold site expected Polynomial.sum
  simp only [ContinuousCriterion.sideMoment, ContinuousCriterion.productMoment,
    ContinuousCriterion.rowMoment]
  fun_prop

theorem upperBound (μ : Measure Coin) [IsProbabilityMeasure μ]
    (P : Polynomial ℝ) (r : ℕ) (α : ℝ≥0)
    (hminor : ∀ x ∈ Set.Ico (0 : ℝ) 1, P.eval x ≤ -Real.log (1-x))
    (hs : Summable (fun h : ℕ => (ContinuousCriterion.moment μ (h+1))^(r+1)/(h+1)))
    (hneg : site P (ContinuousCriterion.moment μ) r α +
      (r : ℝ)*α*(∑' h : ℕ, (ContinuousCriterion.moment μ (h+1))^(r+1)/(h+1)) < 0) :
    Model.UpperBound (r+1) α := by
  obtain ⟨K, hsoft⟩ := PolynomialLog.exists_softened_bound P hminor
  have hm : Filter.Tendsto (fun d => Moments.moment (law μ d)) Filter.atTop
      (nhds (ContinuousCriterion.moment μ)) := tendsto_pi_nhds.mpr
        (fun h => FiniteApproximation.moment_tendsto μ h)
  have ht := (((continuous_site P r α).tendsto (ContinuousCriterion.moment μ)).comp hm).add_const
    ((r : ℝ)*α*(∑' h : ℕ, (ContinuousCriterion.moment μ (h+1))^(r+1)/(h+1)))
  obtain ⟨d, hd⟩ := (ht.eventually_lt_const hneg).exists
  apply finite_upperBound (law μ d) P K hsoft α
  exact (add_le_add_left (mul_le_mul_of_nonneg_left (ContinuousCriterion.correction_le μ r d hs)
    (by positivity : 0 ≤ (r : ℝ)*α)) _).trans_lt hd

end SatFinal.PolynomialCriterion
