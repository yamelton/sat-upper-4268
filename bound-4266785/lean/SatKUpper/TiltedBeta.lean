import SatKUpper.BetaCoin

/-! The quadratic beta tilt, including the endpoint tau = -4. -/

open MeasureTheory SatKUpper.FiniteApproximation SatKUpper.BetaCoin SatKUpper.BetaMoments

namespace SatKUpper.TiltedBeta

noncomputable def weight (τ : ℝ) (x : Coin) : ℝ := 1+τ*x.val*(1-x.val)

theorem weight_bounds {τ : ℝ} (hτ0 : -4 ≤ τ) (hτ1 : τ ≤ 0) (x : Coin) :
    0 ≤ weight τ x ∧ weight τ x ≤ 1 := by
  have h0 := mul_nonneg x.property.1 (sub_nonneg.mpr x.property.2.le)
  have h1 : x.val*(1-x.val) ≤ 1/4 := by nlinarith [sq_nonneg (x.val-1/2)]
  have ht := mul_nonneg (show 0 ≤ τ+4 by linarith) h0
  have hu := mul_nonpos_of_nonpos_of_nonneg hτ1 h0
  unfold weight
  constructor <;> nlinarith

noncomputable def Z (a b τ : ℝ) : ℝ := 1+τ*a*b/((a+b)*(a+b+1))

theorem Z_pos {a b τ : ℝ} (ha : 0 < a) (hb : 0 < b) (hτ : -4 ≤ τ) :
    0 < Z a b τ := by
  have hd : 0 < (a+b)*(a+b+1) := by positivity
  have ht := mul_nonneg (show 0 ≤ τ+4 by linarith) (mul_pos ha hb).le
  have hn : 0 < (a+b)*(a+b+1)+τ*a*b := by nlinarith [sq_nonneg (a-b)]
  have hdiv := div_pos hn hd
  convert hdiv using 1
  unfold Z
  field_simp

theorem weighted_pow_integrable (μ : Measure Coin) [IsProbabilityMeasure μ]
    (τ : ℝ) (h : ℕ) : Integrable (fun x => weight τ x * x.val^h) μ := by
  have he (x : Coin) : weight τ x * x.val^h = x.val^h + τ*(x.val^(h+1)-x.val^(h+2)) := by
    unfold weight
    simp only [pow_succ]
    ring
  simp_rw [he]
  exact (integrable_pow μ h).add (((integrable_pow μ (h+1)).sub
    (integrable_pow μ (h+2))).const_mul τ)

theorem weighted_pow {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (τ : ℝ) (h : ℕ) :
    (∫ x : Coin, weight τ x * x.val^h ∂base a b) =
      u a b h + τ*(u a b (h+1)-u a b (h+2)) := by
  letI := base_probability ha hb
  have he (x : Coin) : weight τ x * x.val^h = x.val^h + τ*(x.val^(h+1)-x.val^(h+2)) := by
    unfold weight
    simp only [pow_succ]
    ring
  simp_rw [he]
  have hi : Integrable (fun x : Coin => τ*(x.val^(h+1)-x.val^(h+2))) (base a b) :=
    ((integrable_pow (base a b) (h+1)).sub (integrable_pow (base a b) (h+2))).const_mul τ
  rw [integral_add (integrable_pow (base a b) h) hi, integral_const_mul,
    integral_sub (integrable_pow (base a b) (h+1)) (integrable_pow (base a b) (h+2))]
  simp_rw [BetaCoin.integral_pow ha hb]

theorem integral_weight {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (τ : ℝ) :
    (∫ x, weight τ x ∂base a b) = Z a b τ := by
  have h := weighted_pow ha hb τ 0
  simp only [pow_zero, mul_one, zero_add] at h
  rw [h]
  simp [u_succ, u_zero, Z]
  field_simp
  ring

noncomputable def measure (a b τ : ℝ) : Measure Coin :=
  (base a b).withDensity (fun x => ENNReal.ofReal (weight τ x / Z a b τ))

theorem measure_probability {a b τ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hτ0 : -4 ≤ τ) (hτ1 : τ ≤ 0) : IsProbabilityMeasure (measure a b τ) := by
  letI := base_probability ha hb
  have hi : Integrable (weight τ) (base a b) := by
    simpa only [pow_zero, mul_one] using weighted_pow_integrable (base a b) τ 0
  have he : (∫ x, weight τ x / Z a b τ ∂base a b) = 1 := by
    rw [integral_div, integral_weight ha hb, div_self (Z_pos ha hb hτ0).ne']
  constructor
  rw [measure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hi.div_const _)
      (Filter.Eventually.of_forall (fun x => div_nonneg (weight_bounds hτ0 hτ1 x).1
        (Z_pos ha hb hτ0).le)), he]
  norm_num

noncomputable def m (a b τ : ℝ) (h : ℕ) : ℝ :=
  u a b h / Z a b τ * (1+τ*b*(a+h)/((a+b+h)*(a+b+h+1)))

theorem moment_identity {a b τ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hτ0 : -4 ≤ τ) (hτ1 : τ ≤ 0) (h : ℕ) :
    (∫ x : Coin, x.val^h ∂measure a b τ) = m a b τ h := by
  have hw : Measurable (fun x : Coin => ENNReal.ofReal (weight τ x / Z a b τ)) := by
    unfold weight
    fun_prop
  rw [measure, integral_withDensity_eq_integral_toReal_smul hw
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (div_nonneg (weight_bounds hτ0 hτ1 _).1
    (Z_pos ha hb hτ0).le), smul_eq_mul]
  simp_rw [div_mul_eq_mul_div]
  rw [integral_div, weighted_pow ha hb]
  unfold m
  simp only [show h+2 = (h+1)+1 by omega, u_succ]
  simp only [Nat.cast_add, Nat.cast_one]
  field_simp
  ring

theorem moment_nonneg {a b τ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hτ0 : -4 ≤ τ) (hτ1 : τ ≤ 0) (h : ℕ) : 0 ≤ m a b τ h := by
  rw [← moment_identity ha hb hτ0 hτ1]
  exact integral_nonneg (fun x => pow_nonneg x.property.1 h)

theorem moment_le {a b τ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hτ0 : -4 ≤ τ) (hτ1 : τ ≤ 0) (h : ℕ) : m a b τ h ≤ u a b h / Z a b τ := by
  have hu : 0 ≤ u a b h / Z a b τ := div_nonneg (u_nonneg ha hb h) (Z_pos ha hb hτ0).le
  unfold m
  apply mul_le_of_le_one_right hu
  have ht : τ*b*(a+h)/((a+b+h)*(a+b+h+1)) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hτ1 hb.le) (by positivity)
  linarith

end SatKUpper.TiltedBeta
