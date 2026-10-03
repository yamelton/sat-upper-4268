import SatUpper.Enclosures
import SatUpper.Series

/-! Rational logarithm enclosures with a proved geometric remainder. -/

namespace SatUpper.LogEnclosures

def logOneSubPartial (x : ℚ) (N : ℕ) : ℚ :=
  - ∑ k ∈ Finset.range N, x ^ (k + 1) / (k + 1)

def logOneSubLower (x : ℚ) (N : ℕ) : ℚ :=
  logOneSubPartial x N - x ^ (N + 1) / (1 - x)

theorem logOneSubPartial_cast (x : ℚ) (N : ℕ) :
    (logOneSubPartial x N : ℝ) = - ∑ k ∈ Finset.range N, (x : ℝ) ^ (k + 1) / (k + 1) := by
  simp [logOneSubPartial]

theorem log_one_sub_enclosure {x : ℚ} (hx0 : 0 ≤ x) (hx1 : x < 1) (N : ℕ) :
    (logOneSubLower x N : ℝ) ≤ Real.log (1 - (x : ℝ)) ∧
      Real.log (1 - (x : ℝ)) ≤ (logOneSubPartial x N : ℝ) := by
  have h0 : (0 : ℝ) ≤ x := by exact_mod_cast hx0
  have h1 : (x : ℝ) < 1 := by exact_mod_cast hx1
  constructor
  · have he := Real.abs_log_sub_add_sum_range_le
      (show |(x : ℝ)| < 1 by rwa [abs_of_nonneg h0]) N
    rw [abs_of_nonneg h0] at he
    have hl := (abs_le.mp he).1
    simp only [logOneSubLower, Rat.cast_sub, Rat.cast_div, Rat.cast_pow, Rat.cast_one,
      logOneSubPartial_cast]
    linarith
  · rw [logOneSubPartial_cast]
    exact log_one_sub_le_neg_partial h0 h1 N

theorem log_two_enclosure (N : ℕ) :
    -(logOneSubPartial (1 / 2) N : ℝ) ≤ Real.log 2 ∧
      Real.log 2 ≤ -(logOneSubLower (1 / 2) N : ℝ) := by
  have h := log_one_sub_enclosure (x := 1 / 2) (by norm_num) (by norm_num) N
  have he : Real.log (1 - ((1 / 2 : ℚ) : ℝ)) = -Real.log 2 := by
    rw [show (1 - ((1 / 2 : ℚ) : ℝ)) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he] at h
  constructor <;> linarith [h.1, h.2]

end SatUpper.LogEnclosures
