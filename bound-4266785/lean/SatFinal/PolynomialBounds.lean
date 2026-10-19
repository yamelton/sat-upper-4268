import SatFinal.PolynomialCriterion

namespace SatFinal.PolynomialBounds
open SatKUpper SatFinal.PolynomialCriterion

noncomputable def fromArray (xs : Array ℚ) : Polynomial ℚ :=
  ∑ h ∈ Finset.range xs.size, Polynomial.monomial h (xs.getD h 0)

noncomputable def realPolynomial (P : Polynomial ℚ) : Polynomial ℝ := P.map (Rat.castHom ℝ)

theorem expected_add (P Q : Polynomial ℝ) (m : ℕ → ℝ) :
    expected (P+Q) m = expected P m+expected Q m := by
  exact Polynomial.sum_add_index P Q _ (by simp) (by intros; ring)

theorem expected_monomial (c : ℝ) (h : ℕ) (m : ℕ → ℝ) :
    expected (Polynomial.monomial h c) m = c*(m h)^2 := by
  exact Polynomial.sum_monomial_index c _ (by simp)

theorem expected_sum {ι : Type*} (s : Finset ι) (P : ι → Polynomial ℝ) (m : ℕ → ℝ) :
    expected (∑ i ∈ s, P i) m = ∑ i ∈ s, expected (P i) m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [expected]
  | @insert i s hi ih => simp [Finset.sum_insert hi, expected_add, ih]

theorem expected_array (xs : Array ℚ) (m : ℕ → ℝ) :
    expected (realPolynomial (fromArray xs)) m =
      ∑ h ∈ Finset.range xs.size, (xs.getD h 0 : ℝ)*(m h)^2 := by
  unfold realPolynomial fromArray
  rw [Polynomial.map_sum, expected_sum]
  simp only [Polynomial.map_monomial, expected_monomial]
  rfl

theorem square_minorant (P R : Polynomial ℚ)
    (hzero : P.eval 0 = 0)
    (hderiv : P.derivative = 2*R-(1-Polynomial.X)*R^2) :
    ∀ x ∈ Set.Ico (0 : ℝ) 1, (realPolynomial P).eval x ≤ -Real.log (1-x) := by
  have hz : (realPolynomial P).eval 0 = 0 := by
    unfold realPolynomial
    rw [Polynomial.eval_map]
    rw [← map_zero (Rat.castHom ℝ), Polynomial.eval₂_at_apply, hzero]
  have hd : (realPolynomial P).derivative =
      2*realPolynomial R-(1-Polynomial.X)*(realPolynomial R)^2 := by
    simp [realPolynomial, Polynomial.derivative_map, hderiv]
  intro x hx
  apply PolynomialLog.square_minorant (R := fun z => (realPolynomial R).eval z) _ hz hx.1 hx.2
  intro z
  simpa only [hd, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_pow] using (realPolynomial P).hasDerivAt z

theorem signed_square {c l u s : ℚ} {v : ℝ}
    (hl0 : 0 ≤ l) (hl : (l : ℝ) ≤ v) (hu : v ≤ (u : ℝ))
    (hs : s ≤ c*(if 0 ≤ c then l else u)^2) : (s : ℝ) ≤ (c : ℝ)*v^2 := by
  have hnonneg : 0 ≤ (l : ℝ) := by exact_mod_cast hl0
  by_cases hc : 0 ≤ c
  · simp only [if_pos hc] at hs
    have hsq : (l : ℝ)^2 ≤ v^2 := by nlinarith
    exact (show (s : ℝ) ≤ (c : ℝ)*(l : ℝ)^2 by exact_mod_cast hs).trans
      (mul_le_mul_of_nonneg_left hsq (by exact_mod_cast hc))
  · simp only [if_neg hc] at hs
    have hsq : v^2 ≤ (u : ℝ)^2 := by nlinarith
    exact (show (s : ℝ) ≤ (c : ℝ)*(u : ℝ)^2 by exact_mod_cast hs).trans
      (mul_le_mul_of_nonpos_left hsq (by exact_mod_cast (le_of_not_ge hc)))

theorem rational_upperBound {α : ℚ} (hα : 0 ≤ α) (P : Polynomial ℚ)
    (hminor : ∀ x ∈ Set.Ico (0 : ℝ) 1, (realPolynomial P).eval x ≤ -Real.log (1-x))
    (H : ℕ) (S : ℚ) (C : ℕ → ℚ) (E : ℚ)
    (hS : (S : ℝ) ≤ expected (realPolynomial P) (ContinuousCriterion.sideMoment Quadratic.m 2 (3*α/2)))
    (hC : ∀ h, h < H → Quadratic.m (h+1)^3/(h+1) ≤ (C h : ℝ))
    (hE : Quadratic.tail (H+1) ≤ (E : ℝ))
    (hneg : -S+2*α*((∑ h ∈ Finset.range H, C h)+E) < 0) :
    Model.UpperBound 3 (α : ℝ) := by
  let aNN : NNReal := ⟨(α : ℝ), by exact_mod_cast hα⟩
  have he : ContinuousCriterion.moment Quadratic.measure = Quadratic.m := funext Quadratic.moment_identity
  apply PolynomialCriterion.upperBound Quadratic.measure (realPolynomial P) 2 aNN hminor
  · rw [he]; exact Quadratic.correction_summable
  · rw [he]
    have hc := Finset.sum_le_sum (fun h (hh : h ∈ Finset.range H) => hC h (Finset.mem_range.mp hh))
    have hsum := add_le_add (neg_le_neg hS)
      (mul_le_mul_of_nonneg_left ((Quadratic.correction_bound H).trans (add_le_add hc hE))
        (show 0 ≤ 2*(α : ℝ) by exact_mod_cast mul_nonneg (by norm_num : (0 : ℚ)≤2) hα))
    have hnegR : -(S : ℝ)+2*(α : ℝ)*
        ((∑ h ∈ Finset.range H, (C h : ℝ))+(E : ℝ)) < 0 := by exact_mod_cast hneg
    simpa only [site, aNN, NNReal.coe_mk, Nat.cast_ofNat,
      show (2 : ℝ)+1=3 by norm_num] using hsum.trans_lt hnegR

end SatFinal.PolynomialBounds
