import SatUpper.Obligations
import SatUpper.Enclosures

/-! Signed interval arithmetic for the alternating vertex moments. -/

namespace SatUpper.VertexEnclosures

def coefficient (k j : ℕ) : ℚ :=
  (-1 : ℚ)^j * (k.factorial / (j.factorial * (k-j).factorial) : ℕ)

theorem coefficient_cast {k j : ℕ} (hj : j ≤ k) :
    (coefficient k j : ℝ) = (-1 : ℝ)^j * (Nat.choose k j : ℝ) := by
  rw [Nat.choose_eq_factorial_div_factorial hj]
  simp [coefficient]

def signedLower (c l u : ℚ) : ℚ := if 0 ≤ c then c*l else c*u

theorem signedLower_le {c l u : ℚ} {x : ℝ}
    (hl : (l : ℝ) ≤ x) (hu : x ≤ (u : ℝ)) :
    (signedLower c l u : ℝ) ≤ (c : ℝ)*x := by
  unfold signedLower
  split_ifs with hc
  · push_cast
    exact mul_le_mul_of_nonneg_left hl (by exact_mod_cast hc)
  · push_cast
    exact mul_le_mul_of_nonpos_left hu (by exact_mod_cast le_of_not_ge hc)

def momentLower (l u : ℕ → ℚ) (k : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (k+1), signedLower (coefficient k j) (l j) (u j)

theorem momentLower_le {l u : ℕ → ℚ} {k : ℕ}
    (hb : ∀ j, j ≤ k → (l j : ℝ) ≤ Formalization.poissonProductMoment j ∧
      Formalization.poissonProductMoment j ≤ (u j : ℝ)) :
    (momentLower l u k : ℝ) ≤ Formalization.noWarningMoment k := by
  unfold momentLower Formalization.noWarningMoment
  push_cast
  apply Finset.sum_le_sum
  intro j hj
  have hjk : j ≤ k := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
  have h := signedLower_le (c := coefficient k j) (hb j hjk).1 (hb j hjk).2
  rwa [coefficient_cast hjk] at h

/-- Squaring a clamped lower endpoint needs no sign assumption on the target. -/
theorem clamped_square_le {l x : ℝ} (h : l ≤ x) : (max 0 l)^2 ≤ x^2 := by
  by_cases hl : 0 ≤ l
  · rw [max_eq_right hl]
    nlinarith
  · rw [max_eq_left (le_of_not_ge hl)]
    simpa using sq_nonneg x

def vertexUpper (K : ℕ) (l u : ℕ → ℚ) : ℚ :=
  -∑ k ∈ Finset.range K, (max 0 (momentLower l u (k+1)))^2 / (k+1)

theorem vertexUpper_correct {K : ℕ} {l u : ℕ → ℚ}
    (hb : ∀ j, j ≤ K → (l j : ℝ) ≤ Formalization.poissonProductMoment j ∧
      Formalization.poissonProductMoment j ≤ (u j : ℝ)) :
    negativeMomentSum K Formalization.noWarningMoment ≤ (vertexUpper K l u : ℝ) := by
  unfold negativeMomentSum vertexUpper
  push_cast
  apply neg_le_neg
  apply Finset.sum_le_sum
  intro k hk
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply clamped_square_le
  apply momentLower_le
  intro j hj
  apply hb j
  have hk' := Finset.mem_range.mp hk
  omega

end SatUpper.VertexEnclosures
