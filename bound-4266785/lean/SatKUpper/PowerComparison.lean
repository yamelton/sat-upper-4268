import SatUpper.Local

/-! The polynomial comparison for every clause size, including odd sizes.
This is a local inequality; it is not the general random k-SAT theorem. -/

namespace SatKUpper.PowerComparison

theorem power_remainder_step (n : ℕ) (x y : ℝ) :
    x ^ (n + 2) - (n + 2 : ℝ) * x * y ^ (n + 1) +
        (n + 1 : ℝ) * y ^ (n + 2) =
      x * (x ^ (n + 1) - (n + 1 : ℝ) * x * y ^ n +
        (n : ℝ) * y ^ (n + 1)) +
      (n + 1 : ℝ) * y ^ n * (x - y) ^ 2 := by
  simp only [pow_succ]
  ring

theorem power_remainder_nonneg (n : ℕ) {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ x ^ (n + 1) - (n + 1 : ℝ) * x * y ^ n +
      (n : ℝ) * y ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Nat.cast_add, Nat.cast_one]
    rw [show (n : ℝ) + 1 + 1 = n + 2 by ring, power_remainder_step]
    exact add_nonneg (mul_nonneg hx ih)
      (mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hy n)) (sq_nonneg _))

end SatKUpper.PowerComparison
