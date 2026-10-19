import SatUpper.Enclosures
import Mathlib.Analysis.Complex.Exponential

/-! Outward-rounded positive Taylor series for exponential certificates.
The state recurrence uses only rational arithmetic and integer rounding. -/

open SatUpper

namespace SatKUpper.TaylorExponential

structure State where
  lowerTerm : ℚ
  upperTerm : ℚ
  lowerSum : ℚ
  upperSum : ℚ
  deriving DecidableEq, Repr

def state (scale : ℕ) (x : ℚ) : ℕ → State
  | 0 => ⟨1,1,1,1⟩
  | n+1 =>
    let p := state scale x n
    let l := Enclosures.lowerOnGrid scale (p.lowerTerm*x/(n+1))
    let u := Enclosures.upperOnGrid scale (p.upperTerm*x/(n+1))
    ⟨l,u,p.lowerSum+l,p.upperSum+u⟩

theorem lower_round_nonneg {scale : ℕ} {x : ℚ} (hx : 0 ≤ x) :
    0 ≤ Enclosures.lowerOnGrid scale x := by
  apply div_nonneg
  · exact_mod_cast Int.floor_nonneg.mpr (mul_nonneg hx (Nat.cast_nonneg scale))
  · exact Nat.cast_nonneg scale

theorem state_nonneg {scale : ℕ} (_hs : 0 < scale) {x : ℚ} (hx : 0 ≤ x) (n : ℕ) :
    0 ≤ (state scale x n).lowerTerm ∧ 1 ≤ (state scale x n).lowerSum := by
  induction n with
  | zero => norm_num [state]
  | succ n ih =>
    have hl := lower_round_nonneg (scale := scale) (show 0 ≤ (state scale x n).lowerTerm*x/(n+1) from
      div_nonneg (mul_nonneg ih.1 hx) (by positivity))
    exact ⟨hl, by change 1 ≤ (state scale x n).lowerSum + _; linarith⟩

theorem term_succ (x : ℝ) (n : ℕ) :
    (x^n/(n.factorial : ℝ))*x/(n+1) = x^(n+1)/((n+1).factorial : ℝ) := by
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  field_simp

theorem state_correct {scale : ℕ} (hs : 0 < scale) {x : ℚ} (hx : 0 ≤ x) (n : ℕ) :
    ((state scale x n).lowerTerm : ℝ) ≤ (x : ℝ)^n/(n.factorial : ℝ) ∧
    (x : ℝ)^n/(n.factorial : ℝ) ≤ ((state scale x n).upperTerm : ℝ) ∧
    ((state scale x n).lowerSum : ℝ) ≤
      (∑ i ∈ Finset.range (n+1), (x : ℝ)^i/(i.factorial : ℝ)) ∧
    (∑ i ∈ Finset.range (n+1), (x : ℝ)^i/(i.factorial : ℝ)) ≤
      ((state scale x n).upperSum : ℝ) := by
  have hxR : (0 : ℝ) ≤ x := by exact_mod_cast hx
  induction n with
  | zero => norm_num [state]
  | succ n ih =>
    have hl := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ih.1 hxR)
      (show (0 : ℝ) ≤ n+1 by positivity)
    have hu := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ih.2.1 hxR)
      (show (0 : ℝ) ≤ n+1 by positivity)
    rw [term_succ] at hl hu
    have hh := Enclosures.rounded_enclosure hs
      (l := (state scale x n).lowerTerm*x/(n+1))
      (u := (state scale x n).upperTerm*x/(n+1))
      (x := (x : ℝ)^(n+1)/((n+1).factorial : ℝ))
      (by exact_mod_cast hl) (by exact_mod_cast hu)
    refine ⟨hh.1, hh.2, ?_, ?_⟩
    · rw [Finset.sum_range_succ]
      simpa only [state, Rat.cast_add] using add_le_add ih.2.2.1 hh.1
    · rw [Finset.sum_range_succ]
      simpa only [state, Rat.cast_add] using add_le_add ih.2.2.2 hh.2

def positiveBounds (scale n : ℕ) (x : ℚ) : ℚ × ℚ :=
  let p := state scale x n
  (p.lowerSum, p.upperSum + 2*Enclosures.upperOnGrid scale (p.upperTerm*x/(n+1)))

theorem positive_correct {scale : ℕ} (hs : 0 < scale) {x : ℚ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (n : ℕ) :
    ((positiveBounds scale n x).1 : ℝ) ≤ Real.exp (x : ℝ) ∧
      Real.exp (x : ℝ) ≤ ((positiveBounds scale n x).2 : ℝ) := by
  have hx0R : (0 : ℝ) ≤ x := by exact_mod_cast hx0
  have hx1R : (x : ℝ) ≤ 1 := by exact_mod_cast hx1
  have h := state_correct hs hx0 n
  have hn := state_correct hs hx0 (n+1)
  refine ⟨h.2.2.1.trans (Real.sum_le_exp_of_nonneg hx0R (n+1)), ?_⟩
  have he := Real.exp_bound' hx0R hx1R (by omega : 0 < n+1)
  simp only [Nat.cast_add, Nat.cast_one] at he
  have hp : (x : ℝ)^(n+1)*(n+1+1)/(((n+1).factorial : ℝ)*(n+1)) ≤
      2*((x : ℝ)^(n+1)/((n+1).factorial : ℝ)) := by
    have hf : (0 : ℝ) < (n+1).factorial := by positivity
    have hd : (0 : ℝ) < n+1 := by positivity
    apply (div_le_iff₀ (mul_pos hf hd)).mpr
    field_simp
    nlinarith [pow_nonneg hx0R (n+1)]
  have hh := he.trans (add_le_add h.2.2.2 (hp.trans (mul_le_mul_of_nonneg_left hn.2.1 (by norm_num))))
  simpa only [positiveBounds, state, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat] using hh

def negativeBounds (scale n : ℕ) (x : ℚ) : ℚ × ℚ :=
  let p := positiveBounds scale n (-x)
  (1/p.2,1/p.1)

theorem negative_correct {scale : ℕ} (hs : 0 < scale) {x : ℚ}
    (hx0 : -1 ≤ x) (hx1 : x ≤ 0) (n : ℕ) :
    ((negativeBounds scale n x).1 : ℝ) ≤ Real.exp (x : ℝ) ∧
      Real.exp (x : ℝ) ≤ ((negativeBounds scale n x).2 : ℝ) := by
  have hx : 0 ≤ -x := neg_nonneg.mpr hx1
  have h := positive_correct hs hx (by linarith : -x ≤ 1) n
  simp only [Rat.cast_neg] at h
  have hl : (0 : ℝ) < (positiveBounds scale n (-x)).1 := by
    have hh := (state_nonneg hs hx n).2
    change 0 < ((state scale (-x) n).lowerSum : ℝ)
    exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℚ) < 1) hh
  have hlo := one_div_le_one_div_of_le (Real.exp_pos (-(x : ℝ))) h.2
  have hhi := one_div_le_one_div_of_le hl h.1
  simpa only [negativeBounds, Rat.cast_div, Rat.cast_one, Rat.cast_neg,
    Real.exp_neg, one_div, Rat.cast_inv, inv_inv] using And.intro hlo hhi

def bounds (scale terms : ℕ) : ℕ → ℚ → ℚ × ℚ
  | 0, x =>
    let p := negativeBounds scale terms x
    (max 0 p.1,p.2)
  | s+1, x =>
    let p := bounds scale terms s (x/2)
    (Enclosures.lowerOnGrid scale (p.1^2), Enclosures.upperOnGrid scale (p.2^2))

theorem bounds_lower_nonneg (scale terms s : ℕ) (x : ℚ) :
    0 ≤ (bounds scale terms s x).1 := by
  cases s with
  | zero => exact le_max_left _ _
  | succ s => exact lower_round_nonneg (sq_nonneg _)

theorem bounds_correct {scale : ℕ} (hs : 0 < scale) (terms s : ℕ) (x : ℚ)
    (hx0 : -(2 : ℚ)^s ≤ x) (hx1 : x ≤ 0) :
    ((bounds scale terms s x).1 : ℝ) ≤ Real.exp (x : ℝ) ∧
      Real.exp (x : ℝ) ≤ ((bounds scale terms s x).2 : ℝ) := by
  induction s generalizing x with
  | zero =>
    have h := negative_correct hs (by simpa using hx0) hx1 terms
    refine ⟨?_, h.2⟩
    simpa only [bounds, Rat.cast_max, Rat.cast_zero] using
      (max_le (Real.exp_pos (x : ℝ)).le h.1)
  | succ s ih =>
    have hhalf : -(2 : ℚ)^s ≤ x/2 := by
      rw [pow_succ] at hx0
      linarith
    have h := ih (x/2) hhalf (div_nonpos_of_nonpos_of_nonneg hx1 (by norm_num))
    have hlo : (0 : ℝ) ≤ (bounds scale terms s (x/2)).1 := by
      exact_mod_cast bounds_lower_nonneg scale terms s (x/2)
    have hl := pow_le_pow_left₀ hlo h.1 2
    have hu := pow_le_pow_left₀ (Real.exp_pos _).le h.2 2
    have he : Real.exp ((x : ℝ)/2)^2 = Real.exp (x : ℝ) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    push_cast at hl hu
    rw [he] at hl hu
    exact Enclosures.rounded_enclosure hs (by exact_mod_cast hl) (by exact_mod_cast hu)

end SatKUpper.TaylorExponential
