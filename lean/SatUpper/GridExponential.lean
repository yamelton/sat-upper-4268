import SatUpper.Enclosures

/-! Exponential enclosures from the tangent bound and repeated squaring. -/

namespace SatUpper.GridExponential

/-- Both endpoints are rounded outwards after each squaring. -/
def bounds (scale : ℕ) : ℕ → ℚ → ℚ × ℚ
  | 0, x => (max 0 (1+x), 1/(1-x))
  | n+1, x =>
    let p := bounds scale n (x/2)
    (Enclosures.lowerOnGrid scale (p.1^2), Enclosures.upperOnGrid scale (p.2^2))

theorem lower_nonneg (scale n : ℕ) (x : ℚ) : 0 ≤ (bounds scale n x).1 := by
  cases n with
  | zero => exact le_max_left _ _
  | succ n =>
    apply div_nonneg
    · exact_mod_cast Int.floor_nonneg.mpr (show (0 : ℚ) ≤
        (bounds scale n (x/2)).1^2 * scale by positivity)
    · exact Nat.cast_nonneg scale

/-- The same elementary tangent inequality gives both endpoints. -/
theorem tangent_bounds {x : ℝ} (hx : x < 1) :
    max 0 (1+x) ≤ Real.exp x ∧ Real.exp x ≤ 1/(1-x) := by
  refine ⟨max_le (Real.exp_pos x).le (by linarith [Real.add_one_le_exp x]), ?_⟩
  have h := one_div_le_one_div_of_le (by linarith : 0 < 1-x)
    (show 1-x ≤ Real.exp (-x) by linarith [Real.add_one_le_exp (-x)])
  simpa [one_div, Real.exp_neg] using h

theorem bounds_correct {scale : ℕ} (hs : 0 < scale) (n : ℕ) (x : ℚ)
    (hx : x < 2^n) :
    ((bounds scale n x).1 : ℝ) ≤ Real.exp (x : ℝ) ∧
      Real.exp (x : ℝ) ≤ ((bounds scale n x).2 : ℝ) := by
  induction n generalizing x with
  | zero =>
    have h := tangent_bounds (x := (x : ℝ)) (by exact_mod_cast hx)
    simpa only [bounds, Rat.cast_max, Rat.cast_zero, Rat.cast_add, Rat.cast_one,
      Rat.cast_div, Rat.cast_sub] using h
  | succ n ih =>
    have hh : x/2 < 2^n := by
      apply (div_lt_iff₀ (by norm_num : (0 : ℚ) < 2)).mpr
      simpa only [pow_succ] using hx
    have h := ih (x/2) hh
    have hlo : (0 : ℝ) ≤ (bounds scale n (x/2)).1 := by exact_mod_cast lower_nonneg scale n (x/2)
    have hl := pow_le_pow_left₀ hlo h.1 2
    have hu := pow_le_pow_left₀ (Real.exp_pos _).le h.2 2
    have he : Real.exp ((x : ℝ)/2)^2 = Real.exp (x : ℝ) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    push_cast at hl hu
    rw [he] at hl hu
    exact Enclosures.rounded_enclosure hs (by exact_mod_cast hl) (by exact_mod_cast hu)

end SatUpper.GridExponential
