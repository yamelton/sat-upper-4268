import Mathlib.Probability.Distributions.Beta
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import SatKUpper.ContinuousCriterion

/-! Exact integer moments of the beta probability measure. The product
formula and recurrence are the inputs used by the analytic certificates. -/

open MeasureTheory ProbabilityTheory

namespace SatKUpper.BetaMoments

theorem pdf_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    0 ≤ betaPDFReal a b x := by
  by_cases hx : 0 < x ∧ x < 1
  · exact (betaPDFReal_pos hx.1 hx.2 ha hb).le
  · simp [betaPDFReal, hx]

theorem integral_density {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (f : ℝ → ℝ) :
    (∫ x, f x ∂betaMeasure a b) = ∫ x, betaPDFReal a b x * f x := by
  unfold betaMeasure betaPDF
  rw [integral_withDensity_eq_integral_toReal_smul
    ((measurable_betaPDFReal a b).ennreal_ofReal)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (pdf_nonneg ha hb _), smul_eq_mul]

theorem integral_pdf {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ x, betaPDFReal a b x) = 1 := by
  letI := isProbabilityMeasureBeta ha hb
  simpa using (integral_density ha hb (fun _ => 1)).symm

theorem pdf_shift {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : ℕ) (x : ℝ) :
    betaPDFReal a b x * x^h = (beta (a+h) b / beta a b) * betaPDFReal (a+h) b x := by
  by_cases hx : 0 < x ∧ x < 1
  · have hah : 0 < a+h := by positivity
    have hp : x ^ (a+(h : ℝ)-1) = x ^ (a-1) * x^h := by
      rw [show a+(h : ℝ)-1 = (a-1)+(h : ℝ) by ring, Real.rpow_add_natCast hx.1.ne']
    simp only [betaPDFReal, if_pos hx, hp]
    field_simp [(beta_pos ha hb).ne', (beta_pos hah hb).ne']
  · simp [betaPDFReal, hx]

theorem integral_pow_ratio {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : ℕ) :
    (∫ x, x^h ∂betaMeasure a b) = beta (a+h) b / beta a b := by
  rw [integral_density ha hb]
  simp_rw [pdf_shift ha hb h]
  rw [integral_const_mul, integral_pdf (by positivity) hb, mul_one]

theorem beta_step {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    beta (a+1) b = (a/(a+b))*beta a b := by
  have hab : 0 < a+b := add_pos ha hb
  simp only [beta, show a+1+b = a+b+1 by ring,
    Real.Gamma_add_one ha.ne', Real.Gamma_add_one hab.ne']
  field_simp

noncomputable def u (a b : ℝ) (h : ℕ) : ℝ :=
  ∏ i ∈ Finset.range h, (a+i)/(a+b+i)

theorem u_zero (a b : ℝ) : u a b 0 = 1 := by simp [u]

theorem u_succ (a b : ℝ) (h : ℕ) :
    u a b (h+1) = u a b h * ((a+h)/(a+b+h)) := by
  unfold u
  rw [Finset.prod_range_succ]

theorem u_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : ℕ) : 0 ≤ u a b h := by
  unfold u
  exact Finset.prod_nonneg (fun _ _ => by positivity)

theorem u_ratio {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : ℕ) :
    u a b h = beta (a+h) b / beta a b := by
  induction h with
  | zero => simp [u_zero, (beta_pos ha hb).ne']
  | succ h ih =>
    rw [u_succ, ih]
    simp only [Nat.cast_add, Nat.cast_one, ← add_assoc]
    rw [beta_step (by positivity : 0 < a+h) hb]
    ring

theorem integral_pow {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : ℕ) :
    (∫ x, x^h ∂betaMeasure a b) = u a b h := by
  rw [integral_pow_ratio ha hb, u_ratio ha hb]

theorem u_products (a b : ℝ) (h : ℕ) :
    u a b h = (∏ i ∈ Finset.range h, (a+i)) / (∏ i ∈ Finset.range h, (a+b+i)) := by
  rw [u, Finset.prod_div_distrib]

theorem ae_support (a b : ℝ) : ∀ᵐ x ∂betaMeasure a b, 0 < x ∧ x < 1 := by
  unfold betaMeasure betaPDF
  rw [ae_withDensity_iff ((measurable_betaPDFReal a b).ennreal_ofReal)]
  filter_upwards [] with x hx
  by_contra h
  exact hx (by simp [betaPDFReal, h])

end SatKUpper.BetaMoments
