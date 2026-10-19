import SatKUpper.FiniteApproximation

/-! Extend the finite-law criterion by downward approximation. Only finite
site moments must converge; the positive correction is bounded termwise. -/

open MeasureTheory SatUpper SatKUpper.Sampling SatKUpper.FiniteApproximation
open scoped NNReal

namespace SatKUpper.ContinuousCriterion

noncomputable def rowMoment (m : ℕ → ℝ) (r j : ℕ) : ℝ :=
  ∑ l ∈ Finset.range (j+1), (-1 : ℝ)^l * (Nat.choose j l : ℝ) * (m l)^r

noncomputable def productMoment (m : ℕ → ℝ) (r : ℕ) (a : ℝ) (j : ℕ) : ℝ :=
  Real.exp (a*(rowMoment m r j-1))

noncomputable def sideMoment (m : ℕ → ℝ) (r : ℕ) (a : ℝ) (h : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (h+1), (-1 : ℝ)^j * (Nat.choose h j : ℝ) * productMoment m r a j

noncomputable def siteValue (m : ℕ → ℝ) (r : ℕ) (α : ℝ) (T : ℕ) : ℝ :=
  negativeMomentSum T (sideMoment m r ((r+1 : ℝ)*α/2))

theorem continuous_siteValue (r T : ℕ) (α : ℝ) :
    Continuous (fun m : ℕ → ℝ => siteValue m r α T) := by
  unfold siteValue negativeMomentSum sideMoment productMoment rowMoment
  fun_prop

theorem finite_side {t : ℕ} (law : CoinLaw t) (r h : ℕ) (a : ℝ) :
    SiteProducts.complementMoment law r a h = sideMoment (Moments.moment law) r a h := by
  unfold SiteProducts.complementMoment sideMoment
  simp_rw [Moments.poisson_moment]
  rfl

theorem finite_value {t : ℕ} (law : CoinLaw t) (r T : ℕ) (α : ℝ) :
    Criterion.value law r α T = siteValue (Moments.moment law) r α T +
      (r : ℝ)*α*EdgeBound.correction law r := by
  unfold Criterion.value siteValue negativeMomentSum
  simp_rw [finite_side]

variable (μ : Measure Coin) [IsProbabilityMeasure μ]

noncomputable def moment (h : ℕ) : ℝ := ∫ x : Coin, x.val^h ∂μ

omit [IsProbabilityMeasure μ] in
theorem moment_nonneg (h : ℕ) : 0 ≤ moment μ h :=
  integral_nonneg (fun x => pow_nonneg x.property.1 h)

theorem correction_le (r d : ℕ)
    (hs : Summable (fun h : ℕ => (moment μ (h+1))^(r+1)/(h+1))) :
    EdgeBound.correction (law μ d) r ≤ ∑' h : ℕ, (moment μ (h+1))^(r+1)/(h+1) := by
  rw [Moments.correction_tsum]
  apply (Moments.correction_hasSum (law μ d) r).summable.tsum_le_tsum _ hs
  intro h
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply pow_le_pow_left₀
    (integral_nonneg (fun z => pow_nonneg ((law μ d).nonneg z) (h+1)))
    (FiniteApproximation.moment_le μ d (h+1))

theorem siteValue_tendsto (r T : ℕ) (α : ℝ) :
    Filter.Tendsto (fun d => siteValue (Moments.moment (law μ d)) r α T)
      Filter.atTop (nhds (siteValue (moment μ) r α T)) := by
  have hm : Filter.Tendsto (fun d => Moments.moment (law μ d)) Filter.atTop
      (nhds (moment μ)) := tendsto_pi_nhds.mpr
        (fun h => FiniteApproximation.moment_tendsto μ h)
  exact ((continuous_siteValue r T α).tendsto (moment μ)).comp hm

theorem upperBound (r T : ℕ) (α : ℝ≥0)
    (hs : Summable (fun h : ℕ => (moment μ (h+1))^(r+1)/(h+1)))
    (hneg : siteValue (moment μ) r α T +
      (r : ℝ)*α*(∑' h : ℕ, (moment μ (h+1))^(r+1)/(h+1)) < 0) :
    Model.UpperBound (r+1) α := by
  have ht := (siteValue_tendsto μ r T α).add_const
    ((r : ℝ)*α*(∑' h : ℕ, (moment μ (h+1))^(r+1)/(h+1)))
  obtain ⟨d, hd⟩ := (ht.eventually_lt_const hneg).exists
  apply Criterion.upperBound (law μ d) α T
  rw [finite_value]
  exact (add_le_add_left (mul_le_mul_of_nonneg_left (correction_le μ r d hs)
    (by positivity : 0 ≤ (r : ℝ)*α)) _).trans_lt hd

end SatKUpper.ContinuousCriterion
