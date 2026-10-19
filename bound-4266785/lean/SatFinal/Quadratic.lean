import SatKUpper.BetaCertificate
import SatKUpper.CertificateBounds

open MeasureTheory SatKUpper SatKUpper.FiniteApproximation SatKUpper.BetaCoin SatKUpper.BetaMoments
open scoped NNReal
namespace SatFinal.Quadratic

noncomputable def weight (x : Coin) : ℝ := 24-34*x.val+37*x.val^2

theorem weight_bounds (x : Coin) : 0 ≤ weight x ∧ weight x ≤ 27 := by
  have h0 := x.property.1
  have h1 := x.property.2.le
  have hx := mul_nonneg h0 (sub_nonneg.mpr h1)
  unfold weight
  constructor
  · nlinarith [sq_nonneg (x.val-17/37)]
  · nlinarith

noncomputable def measure : Measure Coin :=
  (base 1 (4/3)).withDensity (fun x => ENNReal.ofReal (weight x / (663/35)))

theorem weighted_pow_integrable (h : ℕ) :
    Integrable (fun x : Coin => weight x * x.val^h) (base 1 (4/3)) := by
  letI := base_probability (by norm_num : (0 : ℝ)<1) (by norm_num : (0 : ℝ)<4/3)
  have he (x : Coin) : weight x*x.val^h = 24*x.val^h-34*x.val^(h+1)+37*x.val^(h+2) := by
    unfold weight
    simp only [pow_succ]
    ring
  simp_rw [he]
  exact (((integrable_pow _ h).const_mul 24).sub ((integrable_pow _ (h+1)).const_mul 34)).add
    ((integrable_pow _ (h+2)).const_mul 37)

theorem weighted_pow (h : ℕ) :
    (∫ x : Coin, weight x*x.val^h ∂base 1 (4/3)) =
      24*u 1 (4/3) h-34*u 1 (4/3) (h+1)+37*u 1 (4/3) (h+2) := by
  letI := base_probability (by norm_num : (0 : ℝ)<1) (by norm_num : (0 : ℝ)<4/3)
  have he (x : Coin) : weight x*x.val^h = 24*x.val^h-34*x.val^(h+1)+37*x.val^(h+2) := by
    unfold weight
    simp only [pow_succ]
    ring
  simp_rw [he]
  have hi : Integrable (fun x : Coin => 24*x.val^h-34*x.val^(h+1)) (base 1 (4/3)) :=
    ((integrable_pow _ h).const_mul 24).sub ((integrable_pow _ (h+1)).const_mul 34)
  rw [integral_add hi ((integrable_pow _ (h+2)).const_mul 37),
    integral_sub ((integrable_pow _ h).const_mul 24) ((integrable_pow _ (h+1)).const_mul 34)]
  simp_rw [integral_const_mul, BetaCoin.integral_pow (by norm_num : (0 : ℝ)<1)
    (by norm_num : (0 : ℝ)<4/3)]

theorem integral_weight : (∫ x, weight x ∂base 1 (4/3)) = 663/35 := by
  have h := weighted_pow 0
  norm_num [u_succ, u_zero] at h
  exact h

instance measure_probability : IsProbabilityMeasure measure := by
  have hi : Integrable weight (base 1 (4/3)) := by
    simpa only [pow_zero, mul_one] using weighted_pow_integrable 0
  constructor
  rw [measure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hi.div_const _)
      (Filter.Eventually.of_forall (fun x => div_nonneg (weight_bounds x).1 (by norm_num))),
    integral_div, integral_weight]
  norm_num

def multiplier (h : ℕ) : ℚ :=
  35*(81*(h : ℚ)^2+299*h+442)/(221*(3*h+7)*(3*h+10))

noncomputable def m (h : ℕ) : ℝ := u 1 (4/3) h * (multiplier h : ℝ)

theorem multiplier_nonneg (h : ℕ) : 0 ≤ multiplier h := by unfold multiplier; positivity

theorem moment_identity (h : ℕ) : ContinuousCriterion.moment measure h = m h := by
  have hw : Measurable (fun x : Coin => ENNReal.ofReal (weight x/(663/35))) := by
    unfold weight
    fun_prop
  unfold ContinuousCriterion.moment
  rw [measure, integral_withDensity_eq_integral_toReal_smul hw
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (div_nonneg (weight_bounds _).1 (by norm_num : (0 : ℝ)≤663/35)), smul_eq_mul]
  simp_rw [div_mul_eq_mul_div]
  rw [integral_div, weighted_pow]
  unfold m multiplier
  push_cast
  simp only [show h+2=(h+1)+1 by omega, u_succ, Nat.cast_add, Nat.cast_one]
  have h0 : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  field_simp
  ring

theorem beta_shift_two (h : ℕ) :
    u 1 (4/3) h * (70/((3*(h : ℝ)+7)*(3*h+10))) = u 1 (10/3) h := by
  induction h with
  | zero => norm_num [u_zero]
  | succ h ih =>
    rw [u_succ, u_succ, ← ih]
    push_cast
    have hh : (0 : ℝ) ≤ h := Nat.cast_nonneg h
    field_simp
    ring

theorem moment_closed (h : ℕ) :
    m h = u 1 (10/3) h * (81*(h : ℝ)^2+299*h+442)/442 := by
  rw [← beta_shift_two]
  unfold m multiplier
  push_cast
  field_simp
  ring

theorem moment_nonneg (h : ℕ) : 0 ≤ m h := by
  rw [← moment_identity]
  exact ContinuousCriterion.moment_nonneg measure h

theorem moment_le (h : ℕ) : m h ≤ (315/221)*u 1 (4/3) h := by
  have hf : (multiplier h : ℝ) ≤ 315/221 := by
    unfold multiplier
    push_cast
    have hh : (0 : ℝ) ≤ h := Nat.cast_nonneg h
    apply (div_le_iff₀ (by positivity : (0 : ℝ)<221*(3*h+7)*(3*h+10))).mpr
    nlinarith
  exact (mul_le_mul_of_nonneg_left hf (u_nonneg (by norm_num) (by norm_num) h)).trans_eq (mul_comm _ _)

noncomputable def tail (N : ℕ) : ℝ :=
  (315/221)^3 * BetaCertificate.tail 1 (4/3) 0 2 N

theorem tail_bound (N : ℕ) (hN : 0<N) :
    Summable (fun i : ℕ => m (N+i)^3/(N+i : ℕ)) ∧
    (∑' i : ℕ, m (N+i)^3/(N+i : ℕ)) ≤ tail N := by
  have hb := BetaCertificate.tail_bound (by norm_num : (0 : ℝ)<1)
    (by norm_num : (0 : ℝ)<4/3) (by norm_num : (-4 : ℝ)≤0) (by norm_num : (0 : ℝ)≤0) 2 N hN
  simp only [TiltedBeta.m, TiltedBeta.Z, zero_mul, zero_div, add_zero, div_one, mul_one] at hb
  have hs := hb.1.mul_left ((315/221 : ℝ)^3)
  have hd (i : ℕ) : m (N+i)^3/(N+i : ℕ) ≤
      (315/221 : ℝ)^3*(u 1 (4/3) (N+i)^3/(N+i : ℕ)) := by
    calc
      _ ≤ ((315/221)*u 1 (4/3) (N+i))^3/(N+i : ℕ) :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (moment_nonneg _) (moment_le _) 3) (Nat.cast_nonneg _)
      _ = _ := by ring
  have hm := Summable.of_nonneg_of_le
    (fun i => div_nonneg (pow_nonneg (moment_nonneg _) _) (Nat.cast_nonneg _)) hd hs
  refine ⟨hm, ?_⟩
  have he := Summable.tsum_le_tsum hd hm hs
  rw [tsum_mul_left] at he
  exact he.trans (mul_le_mul_of_nonneg_left hb.2 (by positivity))

theorem correction_summable : Summable (fun h : ℕ => m (h+1)^3/(h+1 : ℝ)) := by
  simpa only [Nat.add_comm 1, Nat.cast_add, Nat.cast_one] using (tail_bound 1 (by omega)).1

theorem correction_bound (H : ℕ) :
    (∑' h : ℕ, m (h+1)^3/(h+1 : ℝ)) ≤
    (∑ h ∈ Finset.range H, m (h+1)^3/(h+1 : ℝ)) + tail (H+1) := by
  rw [← correction_summable.sum_add_tsum_nat_add H]
  apply add_le_add_left
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.cast_add, Nat.cast_one, add_assoc] using
    (tail_bound (H+1) (by omega)).2


theorem moment_bounds {h : ℕ} {l u ml mu : ℚ}
    (hl : (l : ℝ) ≤ BetaMoments.u 1 (4/3) h) (hu : BetaMoments.u 1 (4/3) h ≤ (u : ℝ))
    (hml : ml ≤ l*multiplier h) (hmu : u*multiplier h ≤ mu) :
    (ml : ℝ) ≤ m h ∧ m h ≤ (mu : ℝ) := by
  have hm : (0 : ℝ) ≤ (multiplier h : ℚ) := by exact_mod_cast multiplier_nonneg h
  unfold m
  constructor
  · exact (show (ml : ℝ) ≤ (l : ℝ)*(multiplier h : ℚ) by exact_mod_cast hml).trans
      (mul_le_mul_of_nonneg_right hl hm)
  · exact (mul_le_mul_of_nonneg_right hu hm).trans
      (show (u : ℝ)*(multiplier h : ℚ) ≤ (mu : ℝ) by exact_mod_cast hmu)

open ContinuousCriterion

theorem rational_upperBound {α : ℚ} (hα : 0 ≤ α) (T H : ℕ)
    (S C : ℕ → ℚ) (E : ℚ)
    (hS : ∀ h, h < T → (S h : ℝ) ≤ (sideMoment m 2 (3*α/2) (h+1))^2/(h+1))
    (hC : ∀ h, h < H → m (h+1)^3/(h+1) ≤ (C h : ℝ))
    (hE : tail (H+1) ≤ (E : ℝ))
    (hneg : -(∑ h ∈ Finset.range T, S h)+2*α*((∑ h ∈ Finset.range H, C h)+E) < 0) :
    Model.UpperBound 3 (α : ℝ) := by
  let aNN : ℝ≥0 := ⟨(α : ℝ), by exact_mod_cast hα⟩
  have he : ContinuousCriterion.moment measure = m := funext moment_identity
  apply ContinuousCriterion.upperBound measure 2 T aNN
  · rw [he]; exact correction_summable
  · rw [he]
    have hs := Finset.sum_le_sum (fun h (hh : h ∈ Finset.range T) => hS h (Finset.mem_range.mp hh))
    have hc := Finset.sum_le_sum (fun h (hh : h ∈ Finset.range H) => hC h (Finset.mem_range.mp hh))
    have hsum := add_le_add (neg_le_neg hs)
      (mul_le_mul_of_nonneg_left ((correction_bound H).trans (add_le_add hc hE))
        (show 0 ≤ 2*(α : ℝ) by exact_mod_cast mul_nonneg (by norm_num : (0 : ℚ)≤2) hα))
    have hnegR : -(∑ h ∈ Finset.range T, (S h : ℝ))+2*(α : ℝ)*
        ((∑ h ∈ Finset.range H, (C h : ℝ))+(E : ℝ)) < 0 := by exact_mod_cast hneg
    simpa only [siteValue, SatUpper.negativeMomentSum, aNN, NNReal.coe_mk,
      Nat.cast_ofNat, Nat.reduceAdd, show (2 : ℝ)+1=3 by norm_num] using hsum.trans_lt hnegR

end SatFinal.Quadratic
