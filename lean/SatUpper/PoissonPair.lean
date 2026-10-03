import SatUpper.PoissonFunctional
import SatUpper.CompoundPoissonMoments
import SatUpper.Series

/-! Two disjoint classes of Poisson marks. Only their mixed moments are
needed for the vertex bound; no identification of a joint count law is needed. -/

open MeasureTheory SatUpper.PoissonConfiguration SatUpper.PoissonFunctional
open scoped NNReal

namespace SatUpper.PoissonPair

variable {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]

theorem mixed_moment (r : ℝ≥0) (ν : Measure A) [IsProbabilityMeasure ν]
    {f g : A → ℝ} (hf0 : ∀ a, 0 ≤ f a) (hf1 : ∀ a, f a ≤ 1)
    (hg0 : ∀ a, 0 ≤ g a) (hg1 : ∀ a, g a ≤ 1) (hd : ∀ a, f a = 1 ∨ g a = 1) (j k : ℕ) :
    (∫ x, productTest f x ^ j * productTest g x ^ k ∂poisson r ν) =
      Real.exp (r * ((∫ a, f a ^ j ∂ν)-1)) *
        Real.exp (r * ((∫ a, g a ^ k ∂ν)-1)) := by
  have he (x : Configuration A) : productTest f x ^ j * productTest g x ^ k =
      productTest (fun a => f a ^ j * g a ^ k) x := by
    simp [productTest, Finset.prod_mul_distrib, Finset.prod_pow]
  have ha (a : A) : f a ^ j * g a ^ k = f a ^ j + g a ^ k - 1 := by
    rcases hd a with h | h <;> simp [h]
  simp_rw [he]
  rw [PoissonFunctional.integral_poisson_product r ν (measurable_of_countable _)
    (fun a => mul_nonneg (pow_nonneg (hf0 a) _) (pow_nonneg (hg0 a) _))
    (fun a => mul_le_one₀ (pow_le_one₀ (hf0 a) (hf1 a)) (pow_nonneg (hg0 a) _) (pow_le_one₀ (hg0 a) (hg1 a)))]
  simp_rw [ha]
  rw [integral_sub Integrable.of_finite (integrable_const _),
    integral_add Integrable.of_finite Integrable.of_finite,
    integral_const, measureReal_univ_eq_one, one_smul, ← Real.exp_add]
  congr 1
  ring

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The square comes from matching mixed moments, so independence need not
be reconstructed as a separate distributional theorem. -/
theorem complement_moment (μ : Measure Ω) [IsProbabilityMeasure μ]
    {F G : Ω → ℝ} (hF : Measurable F) (hG : Measurable G)
    (hF0 : ∀ x, 0 ≤ F x) (hF1 : ∀ x, F x ≤ 1)
    (hG0 : ∀ x, 0 ≤ G x) (hG1 : ∀ x, G x ≤ 1)
    (M : ℕ → ℝ) (hM : ∀ j k, (∫ x, F x ^ j * G x ^ k ∂μ) = M j * M k)
    (k : ℕ) :
    (∫ x, ((1-F x)*(1-G x))^k ∂μ) =
      (∑ j ∈ Finset.range (k+1), (-1 : ℝ)^j * (Nat.choose k j : ℝ) * M j)^2 := by
  have hi (j l : ℕ) : Integrable (fun x => F x ^ j * G x ^ l) μ := by
    apply (integrable_const (1 : ℝ)).mono' ((hF.pow_const j).mul (hG.pow_const l)).aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (hF0 x) _) (pow_nonneg (hG0 x) _))]
    exact mul_le_one₀ (pow_le_one₀ (hF0 x) (hF1 x)) (pow_nonneg (hG0 x) _) (pow_le_one₀ (hG0 x) (hG1 x))
  let c := fun j => (-1 : ℝ)^j * (Nat.choose k j : ℝ)
  have he (x : Ω) : ((1-F x)*(1-G x))^k =
      ∑ j ∈ Finset.range (k+1), ∑ l ∈ Finset.range (k+1),
        (c j*c l)*(F x^j*G x^l) := by
    simp_rw [mul_pow, CompoundPoissonMoments.complement_pow_expansion,
      Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro l _
    dsimp [c]
    ring
  simp_rw [he]
  rw [integral_finset_sum _ (fun j _ => integrable_finset_sum _ (fun l _ => (hi j l).const_mul _))]
  simp_rw [integral_finset_sum _ (fun l _ => (hi _ l).const_mul _), integral_const_mul, hM,
    pow_two, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  dsimp [c]
  ring

/-- Truncating the softened logarithm costs at most `K*δ`, by Bernoulli's
inequality. The estimate is uniform all the way to a zero hard-conflict factor. -/
theorem softened_log_bound {x δ : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (K : ℕ) :
    Real.log (1-(1-δ)*x) ≤ -(∑ k ∈ Finset.range K, x^(k+1)/(k+1)) + K*δ := by
  have hy0 : 0 ≤ (1-δ)*x := mul_nonneg (sub_nonneg.mpr hδ1) hx0
  have hy1 : (1-δ)*x < 1 := lt_of_le_of_lt
    (mul_le_of_le_one_right (sub_nonneg.mpr hδ1) hx1) (by linarith)
  have ht (k : ℕ) : x^(k+1)/(k+1) - δ ≤ ((1-δ)*x)^(k+1)/(k+1) := by
    have hb := one_add_mul_le_pow (a := -δ) (by linarith) (k+1)
    have hp := mul_le_mul_of_nonneg_right hb (pow_nonneg hx0 (k+1))
    have hu := mul_le_mul_of_nonneg_left (pow_le_one₀ hx0 hx1 (n := k+1))
      (show 0 ≤ (k+1 : ℝ)*δ by positivity)
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < k+1)]
    rw [sub_mul, div_mul_cancel₀ _ (by positivity)]
    simp only [Nat.cast_add, Nat.cast_one, mul_pow, sub_eq_add_neg] at *
    nlinarith
  have hs := Finset.sum_le_sum (s := Finset.range K) (fun k _ => ht k)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
  linarith [log_one_sub_le_neg_partial hy0 hy1 K]

noncomputable def majorant (K : ℕ) (δ A B : ℝ) : ℝ :=
  -(∑ k ∈ Finset.range K, ((1-A)*(1-B))^(k+1)/(k+1)) + K*δ

/-- Symmetric finite upper bound, valid even when either no-warning
probability is zero. -/
theorem log_majorant {A B δ : ℝ} (hA0 : 0 ≤ A) (hA1 : A ≤ 1)
    (hB0 : 0 ≤ B) (hB1 : B ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (K : ℕ) :
    Real.log (noConflict A B + (1-noConflict A B)*δ) ≤ majorant K δ A B := by
  have h0 := mul_nonneg (sub_nonneg.mpr hA1) (sub_nonneg.mpr hB1)
  have h1 : (1-A)*(1-B) ≤ 1 := mul_le_one₀ (by linarith) (by linarith) (by linarith)
  convert softened_log_bound h0 h1 hδ0 hδ1 K using 1
  congr 1
  unfold noConflict
  ring

end SatUpper.PoissonPair
