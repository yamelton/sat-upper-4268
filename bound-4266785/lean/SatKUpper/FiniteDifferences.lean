import SatKUpper.ContinuousCriterion

/-! The binomial transforms in the certificate can be evaluated by a
triangular table of subtractions instead of factorial-sized coefficients. -/

namespace SatKUpper.FiniteDifferences

def coefficient (n j : ℕ) : ℝ := (-1 : ℝ)^j * (Nat.choose n j : ℝ)

noncomputable def transform (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n+1), coefficient n j * f j

theorem coefficient_succ (n j : ℕ) :
    coefficient (n+1) (j+1) = coefficient n (j+1)-coefficient n j := by
  unfold coefficient
  rw [Nat.choose_succ_succ, Nat.cast_add, pow_succ]
  ring

theorem transform_succ (f : ℕ → ℝ) (n : ℕ) :
    transform f (n+1) = transform (fun j => f j-f (j+1)) n := by
  have hshift : (∑ j ∈ Finset.range (n+1), coefficient n (j+1)*f (j+1))+f 0 =
      transform f n := by
    rw [Finset.sum_range_succ]
    simp only [coefficient, Nat.choose_eq_zero_of_lt (Nat.lt_succ_self n),
      Nat.cast_zero, mul_zero, zero_mul, add_zero]
    rw [transform, Finset.sum_range_succ']
    simp [coefficient]
  rw [transform, Finset.sum_range_succ']
  simp_rw [coefficient_succ, sub_mul, Finset.sum_sub_distrib]
  simp only [coefficient, pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, one_mul]
  unfold transform
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  unfold transform coefficient at hshift
  unfold coefficient
  linarith

noncomputable def difference (f : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, i => f i
  | n+1, i => difference f n i-difference f n (i+1)

theorem difference_shift (f : ℕ → ℝ) (n i : ℕ) :
    difference f (n+1) i = difference (fun j => f j-f (j+1)) n i := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    change difference f (n+1) i-difference f (n+1) (i+1) =
      difference (fun j => f j-f (j+1)) n i-difference (fun j => f j-f (j+1)) n (i+1)
    rw [ih, ih]

theorem transform_eq_difference (f : ℕ → ℝ) (n : ℕ) :
    transform f n = difference f n 0 := by
  induction n generalizing f with
  | zero => simp [transform, coefficient, difference]
  | succ n ih => rw [transform_succ, ih, difference_shift]

theorem rowMoment_eq (f : ℕ → ℝ) (r n : ℕ) :
    ContinuousCriterion.rowMoment f r n = difference (fun j => (f j)^r) n 0 :=
  transform_eq_difference _ _

theorem sideMoment_eq (f : ℕ → ℝ) (r n : ℕ) (a : ℝ) :
    ContinuousCriterion.sideMoment f r a n =
      difference (ContinuousCriterion.productMoment f r a) n 0 :=
  transform_eq_difference _ _

end SatKUpper.FiniteDifferences
