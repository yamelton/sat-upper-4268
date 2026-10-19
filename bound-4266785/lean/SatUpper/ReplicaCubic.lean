import SatUpper.ReplicaMoments
import SatUpper.Local

/-! The nonnegative cubic combination of the actual averaged replica moments. -/

open MeasureTheory
open SatUpper.ReplicaMoments

namespace SatUpper.ReplicaCubic

variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]

def mixedFamily (b c : Ξ → Ω → ℝ) (j : Fin 3) : Ξ → Ω → ℝ :=
  if j.val = 0 then b else c

theorem cube_moment (ν : Measure Ξ) (μ : Measure Ω)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure μ] (r : ℕ)
    {b : Ξ → Ω → ℝ} (hb : Measurable (Function.uncurry b))
    (hb0 : ∀ x ω, 0 ≤ b x ω) (hb1 : ∀ x ω, b x ω ≤ 1) :
    productMoment ν μ 3 r (fun _ => b) =
      ∫ v : Fin r → Ω, (replicaAverage ν r b v)^3 ∂Measure.pi (fun _ => μ) := by
  have h := productMoment_eq_replicas ν μ 3 r (fun _ => hb) (fun _ => hb0) (fun _ => hb1)
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h

theorem mixed_moment (ν : Measure Ξ) (μ : Measure Ω)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure μ] (r : ℕ)
    {b c : Ξ → Ω → ℝ} (hb : Measurable (Function.uncurry b))
    (hc : Measurable (Function.uncurry c))
    (hb0 : ∀ x ω, 0 ≤ b x ω) (hb1 : ∀ x ω, b x ω ≤ 1)
    (hc0 : ∀ x ω, 0 ≤ c x ω) (hc1 : ∀ x ω, c x ω ≤ 1) :
    productMoment ν μ 3 r (mixedFamily b c) =
      ∫ v : Fin r → Ω, replicaAverage ν r b v * (replicaAverage ν r c v)^2
        ∂Measure.pi (fun _ => μ) := by
  have hf (j : Fin 3) : Measurable (Function.uncurry (mixedFamily b c j)) := by
    by_cases hj : j.val = 0 <;> simp only [mixedFamily, hj, ite_true, ite_false] <;> assumption
  have h0 (j : Fin 3) (x : Ξ) (ω : Ω) : 0 ≤ mixedFamily b c j x ω := by
    by_cases hj : j.val = 0 <;> simp only [mixedFamily, hj, ite_true, ite_false]
    · exact hb0 x ω
    · exact hc0 x ω
  have h1 (j : Fin 3) (x : Ξ) (ω : Ω) : mixedFamily b c j x ω ≤ 1 := by
    by_cases hj : j.val = 0 <;> simp only [mixedFamily, hj, ite_true, ite_false]
    · exact hb1 x ω
    · exact hc1 x ω
  have h := productMoment_eq_replicas ν μ 3 r hf h0 h1
  simpa [Fin.prod_univ_three, mixedFamily, pow_two, mul_assoc] using h

theorem cubic_moment_nonneg (ν : Measure Ξ) (μ : Measure Ω)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure μ] (r : ℕ)
    {b c : Ξ → Ω → ℝ} (hb : Measurable (Function.uncurry b))
    (hc : Measurable (Function.uncurry c))
    (hb0 : ∀ x ω, 0 ≤ b x ω) (hb1 : ∀ x ω, b x ω ≤ 1)
    (hc0 : ∀ x ω, 0 ≤ c x ω) (hc1 : ∀ x ω, c x ω ≤ 1) :
    0 ≤ productMoment ν μ 3 r (fun _ => b) -
      3*productMoment ν μ 3 r (mixedFamily b c) +
      2*productMoment ν μ 3 r (fun _ => c) := by
  let B := replicaAverage ν r b
  let C := replicaAverage ν r c
  have hB := measurable_replicaAverage ν r hb
  have hC := measurable_replicaAverage ν r hc
  have hBb := replicaAverage_bounds ν r hb hb0 hb1
  have hCb := replicaAverage_bounds ν r hc hc0 hc1
  have hiB : Integrable (fun v => (B v)^3) (Measure.pi (fun _ : Fin r => μ)) :=
    integrable_unit_interval _ (hB.pow_const 3)
      (fun v => pow_nonneg (hBb v).1 3) (fun v => pow_le_one₀ (hBb v).1 (hBb v).2)
  have hiC : Integrable (fun v => (C v)^3) (Measure.pi (fun _ : Fin r => μ)) :=
    integrable_unit_interval _ (hC.pow_const 3)
      (fun v => pow_nonneg (hCb v).1 3) (fun v => pow_le_one₀ (hCb v).1 (hCb v).2)
  have hiBC : Integrable (fun v => B v * (C v)^2) (Measure.pi (fun _ : Fin r => μ)) := by
    apply integrable_unit_interval _ (hB.mul (hC.pow_const 2))
      (fun v => mul_nonneg (hBb v).1 (sq_nonneg _))
    intro v
    exact (mul_le_mul_of_nonneg_right (hBb v).2 (sq_nonneg _)).trans
      (by simpa only [one_mul] using pow_le_one₀ (hCb v).1 (hCb v).2 (n := 2))
  have hi3 : Integrable (fun v => 3*(B v*(C v)^2)) (Measure.pi (fun _ : Fin r => μ)) :=
    hiBC.const_mul 3
  have hi2 : Integrable (fun v => 2*(C v)^3) (Measure.pi (fun _ : Fin r => μ)) :=
    hiC.const_mul 2
  have his : Integrable (fun v => (B v)^3-3*(B v*(C v)^2)) (Measure.pi (fun _ : Fin r => μ)) :=
    hiB.sub hi3
  have h : 0 ≤ ∫ v : Fin r → Ω, (B v)^3-3*(B v*(C v)^2)+2*(C v)^3
      ∂Measure.pi (fun _ => μ) := by
    apply integral_nonneg
    intro v
    simpa only [mul_assoc] using cubic_nonneg (hBb v).1 (hCb v).1
  rw [integral_add his hi2, integral_sub hiB hi3, integral_const_mul, integral_const_mul] at h
  rw [cube_moment ν μ r hb hb0 hb1, mixed_moment ν μ r hb hc hb0 hb1 hc0 hc1,
    cube_moment ν μ r hc hc0 hc1]
  exact h

end SatUpper.ReplicaCubic
