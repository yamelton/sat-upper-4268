import SatFinal.Quadratic
import SatFinal.PolynomialNumerics.Checks
import SatFinal.PolynomialNumerics.ScalarChecks
import SatFinal.PolynomialNumerics.PolynomialIdentity
import SatFinal.PolynomialNumerics.Transforms

/-! Assemble the compact polynomial certificate for 4.266785. -/

open SatFinal.PolynomialNumerics.Data SatKUpper.CertificateBounds

namespace SatFinal.PolynomialNumerics.Checks
open SatKUpper

theorem a_pos : (0 : ℚ) < a := by norm_num [a]
theorem b_pos : (0 : ℚ) < b := by norm_num [b]
theorem tau_lower : (-4 : ℚ) ≤ tau := by norm_num [tau]
theorem tau_upper : tau ≤ (0 : ℚ) := by norm_num [tau]
theorem alpha_nonneg : (0 : ℚ) ≤ alpha := by norm_num [alpha]
theorem momentScale_pos : 0 < momentScale := by decide +kernel
theorem expScale_pos : 0 < expScale := by decide +kernel
theorem internalScale_pos : 0 < internalScale := by decide +kernel

noncomputable abbrev realMoment := SatFinal.Quadratic.m
noncomputable abbrev realLambda : ℝ := 3*(alpha : ℝ)/2

theorem raw_bounds (h : ℕ) (hh : h ≤ 513) :
    (lower raw momentScale h : ℝ) ≤ BetaMoments.u a b h ∧
      BetaMoments.u a b h ≤ (upper raw momentScale h : ℝ) :=
  BetaEnclosures.recurrence_bounds a_pos b_pos (lower raw momentScale)
    (upper raw momentScale) 513 raw_initial (fun i hi => raw_steps ⟨i,hi⟩) h hh

theorem moment_bounds (h : ℕ) (hh : h ≤ 513) :
    (lower moments momentScale h : ℝ) ≤ realMoment h ∧
      realMoment h ≤ (upper moments momentScale h : ℝ) := by
  have hr := raw_bounds h hh
  simp only [a, b, Rat.cast_one, Rat.cast_div, Rat.cast_ofNat] at hr
  have hc := moment_steps ⟨h,by omega⟩
  exact SatFinal.Quadratic.moment_bounds hr.1 hr.2 hc.1 hc.2

theorem realMoment_nonneg (h : ℕ) : 0 ≤ realMoment h :=
  SatFinal.Quadratic.moment_nonneg h

theorem power_encloses : DifferenceEnclosures.Encloses momentScale powers.toList
    (fun j => (realMoment j)^2) := by
  apply encloses_toList momentScale_pos
  intro j hj
  have hj' : j < 193 := by simpa only [sizes.2.2.1] using hj
  have hm := moment_bounds j (by omega)
  have hc := power_steps ⟨j,hj'⟩
  exact BetaEnclosures.power_bounds (realMoment_nonneg j) hc.1 hm.1 hm.2 2 hc.2.1 hc.2.2

theorem nu_encloses : DifferenceEnclosures.Encloses momentScale nu.toList
    (ContinuousCriterion.rowMoment realMoment 2) := by
  have h := DifferenceEnclosures.table_correct power_encloses 193
    (by simp only [Array.length_toList, sizes.2.2.1]; rfl)
  rw [nu_table] at h
  intro i hi
  simpa only [FiniteDifferences.rowMoment_eq] using h i hi

theorem compound_bounds (hExp : ∀ j : Fin 193, expStep j) (j : ℕ) (hj : j < 193) :
    (lower compound expScale j : ℝ) ≤ ContinuousCriterion.productMoment realMoment 2 realLambda j ∧
      ContinuousCriterion.productMoment realMoment 2 realLambda j ≤ (upper compound expScale j : ℝ) := by
  have hn := bounds_of_encloses momentScale_pos nu_encloses j
    (by simpa only [sizes.2.2.2.1] using hj)
  have hc := argument_steps ⟨j,hj⟩
  have he := hExp ⟨j,hj⟩
  have hlam : 0 ≤ realLambda := by norm_num [realLambda, alpha]
  have hl : (lower arguments argumentScale j : ℝ) ≤
      realLambda*(ContinuousCriterion.rowMoment realMoment 2 j-1) := by
    have ht := (Rat.cast_le (K := ℝ)).mpr hc.1
    have hh : (lower arguments argumentScale j : ℝ) ≤ realLambda*((lower nu momentScale j : ℝ)-1) := by
      simpa only [realLambda, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat,
        Rat.cast_sub, Rat.cast_one] using ht
    exact hh.trans (mul_le_mul_of_nonneg_left (sub_le_sub_right hn.1 1) hlam)
  have hu : realLambda*(ContinuousCriterion.rowMoment realMoment 2 j-1) ≤
      (upper arguments argumentScale j : ℝ) := by
    have ht := (Rat.cast_le (K := ℝ)).mpr hc.2.1
    have hh : realLambda*((upper nu momentScale j : ℝ)-1) ≤ (upper arguments argumentScale j : ℝ) := by
      simpa only [realLambda, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat,
        Rat.cast_sub, Rat.cast_one] using ht
    exact (mul_le_mul_of_nonneg_left (sub_le_sub_right hn.2 1) hlam).trans hh
  exact exponential_bounds_single internalScale_pos hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2 hl hu he.1 he.2

theorem side_encloses (hExp : ∀ j : Fin 193, expStep j) :
    DifferenceEnclosures.Encloses expScale side.toList
      (ContinuousCriterion.sideMoment realMoment 2 realLambda) := by
  have hc : DifferenceEnclosures.Encloses expScale compound.toList
      (ContinuousCriterion.productMoment realMoment 2 realLambda) := by
    apply encloses_toList expScale_pos
    intro j hj
    exact compound_bounds hExp j (by simpa only [sizes.2.2.2.2.2.1] using hj)
  have h := DifferenceEnclosures.table_correct hc 193
    (by simp only [Array.length_toList, sizes.2.2.2.2.2.1]; rfl)
  rw [side_table] at h
  intro i hi
  simpa only [FiniteDifferences.sideMoment_eq] using h i hi

theorem upperBound : Model.UpperBound 3 (853357/200000 : ℝ) := by
  have ha : (alpha : ℝ) = 853357/200000 := by norm_num [alpha]
  rw [← ha]
  apply SatFinal.PolynomialBounds.rational_upperBound alpha_nonneg
    (SatFinal.PolynomialBounds.fromArray coefficients) polynomial_minorant 512
    (∑ h ∈ Finset.range 193, signedTerm h) (fun h => term correctionTerms (h+1))
    ((Data.tailUpper : ℚ)/finalScale)
  · rw [SatFinal.PolynomialBounds.expected_array, coefficients_size]
    push_cast
    apply Finset.sum_le_sum
    intro h hh
    have hm := bounds_of_encloses expScale_pos (side_encloses exp_steps) h
      (by rw [sizes.2.2.2.2.2.2]; exact Finset.mem_range.mp hh)
    have hc := site_steps ⟨h,Finset.mem_range.mp hh⟩
    simpa only [coefficient, realMoment, realLambda] using
      SatFinal.PolynomialBounds.signed_square hc.1 hm.1 hm.2 hc.2
  · intro h hh
    exact correction_term (realMoment_nonneg (h+1)) (moment_bounds (h+1) (by omega)).2
      3 h (correction_steps ⟨h,hh⟩)
  · have ht := tail_upper a_pos b_pos tau_lower 2 513 (by omega) (raw_bounds 513 (by omega)).2
    have hm := mul_le_mul_of_nonneg_left ht (by norm_num : (0 : ℝ) ≤ (315/221)^3)
    have hm' : SatFinal.Quadratic.tail 513 ≤
        (((315/221 : ℚ)^3 * CertificateBounds.tailUpper a b tau (upper raw momentScale 513) 2 513 : ℚ) : ℝ) := by
      simpa only [SatFinal.Quadratic.tail, a, b, tau, Rat.cast_mul, Rat.cast_pow,
        Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Rat.cast_zero] using hm
    exact hm'.trans (by exact_mod_cast tail_step)
  · exact final_negative

end SatFinal.PolynomialNumerics.Checks
