import SatKUpper.BetaEnclosures
import SatKUpper.DifferenceEnclosures
import SatKUpper.TaylorExponential
import SatUpper.VertexEnclosures

/-! Assemble checked rational tables into the analytic beta certificate. -/

open SatKUpper.ContinuousCriterion
open scoped NNReal

namespace SatKUpper.CertificateBounds

abbrev Interval := DifferenceEnclosures.Interval

def lower (xs : Array Interval) (scale i : ℕ) : ℚ := ((xs.getD i (0,0)).1 : ℚ)/scale
def upper (xs : Array Interval) (scale i : ℕ) : ℚ := ((xs.getD i (0,0)).2 : ℚ)/scale

theorem getD_toList (xs : Array Interval) (i : ℕ) :
    xs.toList.getD i (0,0) = xs.getD i (0,0) := by
  by_cases hi : i < xs.size <;> simp [List.getD, Array.getD, hi]

theorem encloses_toList {xs : Array Interval} {scale : ℕ} (hs : 0 < scale) {f : ℕ → ℝ}
    (hb : ∀ i, i < xs.size → (lower xs scale i : ℝ) ≤ f i ∧ f i ≤ (upper xs scale i : ℝ)) :
    DifferenceEnclosures.Encloses scale xs.toList f := by
  intro i hi
  have h := hb i (by simpa using hi)
  have hsR : (0 : ℝ) < scale := by exact_mod_cast hs
  simp only [lower, upper, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] at h
  rw [getD_toList]
  exact ⟨by nlinarith [(div_le_iff₀ hsR).mp h.1], by nlinarith [(le_div_iff₀ hsR).mp h.2]⟩

theorem bounds_of_encloses {xs : Array Interval} {scale : ℕ} (hs : 0 < scale) {f : ℕ → ℝ}
    (hb : DifferenceEnclosures.Encloses scale xs.toList f) (i : ℕ) (hi : i < xs.size) :
    (lower xs scale i : ℝ) ≤ f i ∧ f i ≤ (upper xs scale i : ℝ) := by
  have h := hb i (by simpa using hi)
  have hsR : (0 : ℝ) < scale := by exact_mod_cast hs
  rw [getD_toList] at h
  simp only [lower, upper, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
  exact ⟨(div_le_iff₀ hsR).mpr (by nlinarith [h.1]), (le_div_iff₀ hsR).mpr (by nlinarith [h.2])⟩

theorem exponential_bounds {scale terms s : ℕ} (hs : 0 < scale)
    {xl xu l u : ℚ} {x : ℝ} (hxl0 : -(2 : ℚ)^s ≤ xl) (hxl1 : xl ≤ 0)
    (hxu0 : -(2 : ℚ)^s ≤ xu) (hxu1 : xu ≤ 0)
    (hxl : (xl : ℝ) ≤ x) (hxu : x ≤ (xu : ℝ))
    (hl : l ≤ (TaylorExponential.bounds scale terms s xl).1)
    (hu : (TaylorExponential.bounds scale terms s xu).2 ≤ u) :
    (l : ℝ) ≤ Real.exp x ∧ Real.exp x ≤ (u : ℝ) := by
  have hb0 := TaylorExponential.bounds_correct hs terms s xl hxl0 hxl1
  have hb1 := TaylorExponential.bounds_correct hs terms s xu hxu0 hxu1
  exact ⟨(show (l : ℝ) ≤ (TaylorExponential.bounds scale terms s xl).1 by exact_mod_cast hl).trans
      (hb0.1.trans (Real.exp_le_exp.mpr hxl)),
    (Real.exp_le_exp.mpr hxu).trans (hb1.2.trans
      (show ((TaylorExponential.bounds scale terms s xu).2 : ℝ) ≤ u by exact_mod_cast hu))⟩

theorem exp_sub_le {x y : ℝ} (hxy : x ≤ y) (hy : y ≤ 0) :
    Real.exp y-Real.exp x ≤ y-x := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (x-y)) (Real.exp_pos y).le
  rw [← Real.exp_add, show y+(x-y) = x by ring] at h
  have hu := mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr hy) (sub_nonneg.mpr hxy)
  nlinarith

theorem exponential_bounds_single {scale terms s : ℕ} (hs : 0 < scale)
    {xl xu l u : ℚ} {x : ℝ} (hxl0 : -(2 : ℚ)^s ≤ xl) (hxl1 : xl ≤ 0) (hxu1 : xu ≤ 0)
    (hxl : (xl : ℝ) ≤ x) (hxu : x ≤ (xu : ℝ))
    (hl : l ≤ (TaylorExponential.bounds scale terms s xl).1)
    (hu : (TaylorExponential.bounds scale terms s xl).2+(xu-xl) ≤ u) :
    (l : ℝ) ≤ Real.exp x ∧ Real.exp x ≤ (u : ℝ) := by
  have hb := TaylorExponential.bounds_correct hs terms s xl hxl0 hxl1
  refine ⟨(show (l : ℝ) ≤ (TaylorExponential.bounds scale terms s xl).1 by exact_mod_cast hl).trans
    (hb.1.trans (Real.exp_le_exp.mpr hxl)), ?_⟩
  have hd := exp_sub_le hxl (hxu.trans (by exact_mod_cast hxu1))
  have huR : ((TaylorExponential.bounds scale terms s xl).2 : ℝ)+((xu : ℝ)-(xl : ℝ)) ≤ u :=
    by exact_mod_cast hu
  linarith [hb.2]

theorem site_term {l q : ℚ} {x : ℝ} (hl : (l : ℝ) ≤ x) (h : ℕ)
    (hq : q ≤ (max 0 l)^2/(h+1)) : (q : ℝ) ≤ x^2/(h+1) := by
  have hc := SatUpper.VertexEnclosures.clamped_square_le hl
  exact (show (q : ℝ) ≤ (max 0 (l : ℝ))^2/(h+1) by exact_mod_cast hq).trans
    (div_le_div_of_nonneg_right hc (by positivity))

theorem correction_term {u q : ℚ} {x : ℝ} (hx : 0 ≤ x) (hu : x ≤ (u : ℝ))
    (k h : ℕ) (hq : u^k/(h+1) ≤ q) : x^k/(h+1) ≤ (q : ℝ) :=
  (div_le_div_of_nonneg_right (pow_le_pow_left₀ hx hu k) (by positivity)).trans
    (by exact_mod_cast hq)

def tailUpper (a b τ U : ℚ) (r N : ℕ) : ℚ :=
  U^(r+1)/(BetaEnclosures.normalizer a b τ^(r+1)*N) *
    (1+(a+b+N)/((r+1 : ℚ)*b))

theorem tail_upper {a b τ U : ℚ} (ha : 0 < a) (hb : 0 < b) (ht : -4 ≤ τ)
    (r N : ℕ) (hN : 0 < N) (hU : BetaMoments.u a b N ≤ (U : ℝ)) :
    BetaCertificate.tail a b τ r N ≤ (tailUpper a b τ U r N : ℝ) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hz := TiltedBeta.Z_pos haR hbR (by exact_mod_cast ht : (-4 : ℝ) ≤ τ)
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  unfold BetaCertificate.tail tailUpper
  push_cast
  rw [BetaEnclosures.normalizer_cast]
  apply mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (pow_le_pow_left₀ (BetaMoments.u_nonneg haR hbR N) hU _) (by positivity))
    (by positivity)

theorem upperBound {a b τ α : ℚ} (ha : 0 < a) (hb : 0 < b) (ht0 : -4 ≤ τ)
    (ht1 : τ ≤ 0) (hα : 0 ≤ α) (r T H : ℕ)
    (S C : ℕ → ℚ) (E : ℚ)
    (hS : ∀ h, h < T → (S h : ℝ) ≤
      (sideMoment (TiltedBeta.m a b τ) r ((r+1 : ℝ)*α/2) (h+1))^2/(h+1))
    (hC : ∀ h, h < H → TiltedBeta.m a b τ (h+1)^(r+1)/(h+1) ≤ (C h : ℝ))
    (hE : BetaCertificate.tail a b τ r (H+1) ≤ (E : ℝ))
    (hneg : -(∑ h ∈ Finset.range T, S h)+(r : ℚ)*α*((∑ h ∈ Finset.range H, C h)+E) < 0) :
    Model.UpperBound (r+1) (α : ℝ) := by
  let aNN : ℝ≥0 := ⟨(α : ℝ), by exact_mod_cast hα⟩
  apply BetaCertificate.upperBound (a := (a : ℝ)) (b := (b : ℝ)) (τ := (τ : ℝ)) (by exact_mod_cast ha) (by exact_mod_cast hb)
    (by exact_mod_cast ht0) (by exact_mod_cast ht1) r aNN T H
  have hs := Finset.sum_le_sum (fun h (hh : h ∈ Finset.range T) => hS h (Finset.mem_range.mp hh))
  have hc := Finset.sum_le_sum (fun h (hh : h ∈ Finset.range H) => hC h (Finset.mem_range.mp hh))
  have hsum := add_le_add (neg_le_neg hs)
    (mul_le_mul_of_nonneg_left (add_le_add hc hE)
      (show 0 ≤ (r : ℝ)*(α : ℝ) by exact_mod_cast mul_nonneg (Nat.cast_nonneg r) hα))
  have hnegR : -(∑ h ∈ Finset.range T, (S h : ℝ))+(r : ℝ)*α*
      ((∑ h ∈ Finset.range H, (C h : ℝ))+(E : ℝ)) < 0 := by exact_mod_cast hneg
  exact hsum.trans_lt hnegR

end SatKUpper.CertificateBounds
