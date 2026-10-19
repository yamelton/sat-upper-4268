import SatFinal.PolynomialBounds

/-! Reduce the polynomial square identity to finite rational coefficient checks. -/
namespace SatFinal.PolynomialCoefficients
open SatFinal.PolynomialBounds

theorem array_coeff (xs : Array ℚ) (h : ℕ) : (fromArray xs).coeff h = xs.getD h 0 := by
  unfold fromArray
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single h]
  · simp
  · intro b hb hne
    simp [hne]
  · intro hh
    have hn : ¬ h < xs.size := by simpa using hh
    simp [Array.getD, hn]

theorem array_degree (xs : Array ℚ) : (fromArray xs).natDegree ≤ xs.size-1 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [array_coeff]
  simp [Array.getD, show ¬n<xs.size by omega]

def squareCoeff (xs : Array ℚ) (h : ℕ) : ℚ :=
  ∑ ij ∈ Finset.antidiagonal h, xs.getD ij.1 0 * xs.getD ij.2 0

def rhsCoeff (xs : Array ℚ) (h : ℕ) : ℚ :=
  2*xs.getD h 0-squareCoeff xs h + if h=0 then 0 else squareCoeff xs (h-1)

theorem square_coeff (xs : Array ℚ) (h : ℕ) :
    ((fromArray xs)^2).coeff h = squareCoeff xs h := by
  simp only [pow_two, Polynomial.coeff_mul, array_coeff, squareCoeff]

theorem rhs_coeff (xs : Array ℚ) (h : ℕ) :
    (2*fromArray xs-(1-Polynomial.X)*(fromArray xs)^2).coeff h = rhsCoeff xs h := by
  rw [show 2*fromArray xs-(1-Polynomial.X)*(fromArray xs)^2 =
      (2*fromArray xs-(fromArray xs)^2)+Polynomial.X*(fromArray xs)^2 by ring]
  simp only [Polynomial.coeff_add, Polynomial.coeff_sub]
  change ((2 : ℕ)*fromArray xs).coeff h-_+_ = _
  rw [Polynomial.coeff_natCast_mul, array_coeff, square_coeff]
  cases h with
  | zero => simp [rhsCoeff]
  | succ h => simp [Polynomial.coeff_X_mul, square_coeff, rhsCoeff]

theorem identity (P R : Array ℚ) (N : ℕ)
    (hP : P.size ≤ N+1) (hR : 2*R.size+1 ≤ N)
    (hcheck : ∀ h, h ≤ N → P.getD (h+1) 0*(h+1) = rhsCoeff R h) :
    (fromArray P).derivative = 2*fromArray R-(1-Polynomial.X)*(fromArray R)^2 := by
  have hp : (fromArray P).derivative.natDegree ≤ N :=
    (Polynomial.natDegree_derivative_le _).trans (by have := array_degree P; omega)
  have hr := array_degree R
  have h2 : ((2 : Polynomial ℚ)*fromArray R).natDegree ≤ (fromArray R).natDegree := by
    have h := @Polynomial.natDegree_mul_le ℚ _ (2 : Polynomial ℚ) (fromArray R)
    simpa using h
  have hs := @Polynomial.natDegree_pow_le ℚ _ (fromArray R) 2
  have hx := @Polynomial.natDegree_mul_le ℚ _ Polynomial.X ((fromArray R)^2)
  rw [Polynomial.natDegree_X] at hx
  have hq : (2*fromArray R-(1-Polynomial.X)*(fromArray R)^2).natDegree ≤ N := by
    rw [show 2*fromArray R-(1-Polynomial.X)*(fromArray R)^2 =
      (2*fromArray R-(fromArray R)^2)+Polynomial.X*(fromArray R)^2 by ring]
    exact (Polynomial.natDegree_add_le _ _).trans (max_le
      ((Polynomial.natDegree_sub_le _ _).trans (max_le (by omega) (by omega))) (by omega))
  apply (Polynomial.ext_iff_natDegree_le hp hq).mpr
  intro h hh
  rw [Polynomial.coeff_derivative, array_coeff, rhs_coeff]
  exact hcheck h hh

end SatFinal.PolynomialCoefficients
