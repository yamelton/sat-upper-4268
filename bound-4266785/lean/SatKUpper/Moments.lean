import SatKUpper.Criterion

/-! Evaluate the criterion through the moments of the finite coin law. -/

open MeasureTheory SatUpper SatKUpper.Sampling SatKUpper.SiteVertex SatKUpper.SiteProducts

namespace SatKUpper.Moments

variable {t : ℕ} (law : CoinLaw t)

noncomputable def moment (h : ℕ) : ℝ := ∫ z, law.rate z ^ h ∂law.measure

theorem product_moment (k h : ℕ) :
    (∫ z, (∏ j, law.rate (z j))^h ∂markLaw law k) = (moment law h)^k := by
  simp_rw [← Finset.prod_pow]
  have hp := integral_fintype_prod_eq_prod (μ := fun _ : Fin k => law.measure)
    (fun _ z => law.rate z ^ h : Fin k → Fin t → ℝ)
  simpa [markLaw, moment] using hp

theorem mark_moment (r h : ℕ) :
    (∫ z, mark law z ^ h ∂markLaw law r) =
      ∑ j ∈ Finset.range (h+1), (-1 : ℝ)^j * (Nat.choose h j : ℝ) * (moment law j)^r := by
  simp_rw [mark, CompoundPoissonMoments.complement_pow_expansion]
  rw [integral_finset_sum _ (fun _ _ => Integrable.of_finite)]
  simp_rw [integral_const_mul, product_moment]

theorem poisson_moment (r h : ℕ) (a : ℝ) :
    poissonMoment law r a h = Real.exp (a *
      ((∑ j ∈ Finset.range (h+1), (-1 : ℝ)^j * (Nat.choose h j : ℝ) * (moment law j)^r)-1)) := by
  rw [poissonMoment, mark_moment]

theorem correction_hasSum (r : ℕ) :
    HasSum (fun h : ℕ => (moment law (h+1))^(r+1)/(h+1))
      (EdgeBound.correction law r) := by
  have hs (z : Mark t (r+1)) :
      HasSum (fun h : ℕ => (∏ j, law.rate (z j))^(h+1)/(h+1))
        (-Real.log (1-∏ j, law.rate (z j))) :=
    Real.hasSum_pow_div_log_of_abs_lt_one
      (by rw [abs_of_nonneg (EdgeBound.product_bounds law z).1]
          exact (EdgeBound.product_bounds law z).2)
  have hh := hasSum_sum (s := Finset.univ) (fun z _ =>
    (hs z).mul_left ((markLaw law (r+1)).real {z}))
  have he (h : ℕ) : (moment law (h+1))^(r+1)/(h+1) =
      ∑ z : Mark t (r+1), (markLaw law (r+1)).real {z} *
        ((∏ j, law.rate (z j))^(h+1)/(h+1)) := by
    rw [← product_moment, ← integral_div]
    simpa only [smul_eq_mul] using integral_fintype _ Integrable.of_finite
  have hc : EdgeBound.correction law r =
      ∑ z : Mark t (r+1), (markLaw law (r+1)).real {z} *
        (-Real.log (1-∏ j, law.rate (z j))) := by
    rw [EdgeBound.correction, ← integral_neg]
    simpa only [smul_eq_mul] using integral_fintype _ Integrable.of_finite
  simpa only [← he, ← hc] using hh

theorem correction_tsum (r : ℕ) :
    EdgeBound.correction law r = ∑' h : ℕ, (moment law (h+1))^(r+1)/(h+1) :=
  (correction_hasSum law r).tsum_eq.symm

theorem criterion_value (r T : ℕ) (α : ℝ) :
    Criterion.value law r α T =
      negativeMomentSum T (complementMoment law r ((r+1 : ℝ)*α/2)) +
        (r : ℝ)*α*(∑' h : ℕ, (moment law (h+1))^(r+1)/(h+1)) := by
  rw [Criterion.value, correction_tsum]

end SatKUpper.Moments
