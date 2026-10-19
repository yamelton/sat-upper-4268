import SatFinal.Quadratic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! A polynomial lower bound for the logarithm, certified by one square. -/

open Set
namespace SatFinal.PolynomialLog

theorem log_minorant {P D : ℝ → ℝ} (hP : ∀ x, HasDerivAt P (D x) x)
    (hzero : P 0 = 0)
    (hD : ∀ x ∈ Ico (0 : ℝ) 1, (1-x)*D x ≤ 1)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) : P x ≤ -Real.log (1-x) := by
  let f := fun x => -Real.log (1-x)-P x
  have hd (z : ℝ) (hz : z < 1) :
      HasDerivAt f (1/(1-z)-D z) z := by
    have h := (((hasDerivAt_id z).const_sub 1).log (by linarith : 1-z ≠ 0)).neg.sub (hP z)
    convert h using 1
    simp
    ring
  have hc : ContinuousOn f (Ico (0 : ℝ) 1) := fun z hz =>
    (hd z hz.2).continuousAt.continuousWithinAt
  have hm : MonotoneOn f (Ico (0 : ℝ) 1) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico _ _) hc
      (fun z hz => (hd z (interior_subset hz).2).hasDerivWithinAt)
      (fun z hz => by
        have hz' := interior_subset hz
        have hh := hD z hz'
        have hp : 0 < 1-z := by linarith [hz'.2]
        apply sub_nonneg.mpr
        exact (le_div_iff₀ hp).mpr (by nlinarith))
  have h := hm (by constructor <;> norm_num) ⟨hx0,hx1⟩ hx0
  simpa [f, hzero] using h

theorem square_minorant {P R : ℝ → ℝ}
    (hP : ∀ x, HasDerivAt P (2*R x-(1-x)*(R x)^2) x) (hzero : P 0 = 0)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) : P x ≤ -Real.log (1-x) := by
  apply log_minorant hP hzero _ hx0 hx1
  intro z hz
  nlinarith [sq_nonneg (1-(1-z)*R z)]

theorem exists_softened_bound (P : Polynomial ℝ)
    (hminor : ∀ x ∈ Ico (0 : ℝ) 1, P.eval x ≤ -Real.log (1-x)) :
    ∃ K : ℕ, ∀ x ∈ Icc (0 : ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      Real.log (1-(1-δ)*x) ≤ -P.eval x + K*δ := by
  have hb := isCompact_Icc.bddAbove_image
    (P.derivative.differentiable.continuous.norm.continuousOn :
      ContinuousOn (fun x : ℝ => ‖P.derivative.eval x‖) (Icc 0 1))
  obtain ⟨C, hC⟩ := bddAbove_def.mp hb
  obtain ⟨K, hK⟩ := exists_nat_ge C
  refine ⟨K, ?_⟩
  intro x hx δ hδ0 hδ1
  have hy0 : 0 ≤ (1-δ)*x := mul_nonneg (by linarith) hx.1
  have hy1 : (1-δ)*x < 1 := (mul_le_of_le_one_right (by linarith) hx.2).trans_lt (by linarith)
  have hyx : (1-δ)*x ≤ x := by nlinarith [hx.1]
  have hd := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z _ => P.hasDerivWithinAt z _) (fun z hz => (hC _ ⟨z,hz,rfl⟩).trans hK)
    ⟨hy0,hy1.le⟩ hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hyx)] at hd
  have he : x-(1-δ)*x ≤ δ := by nlinarith [hx.2]
  have hh := (le_abs_self (P.eval x-P.eval ((1-δ)*x))).trans
    (hd.trans (mul_le_mul_of_nonneg_left he (Nat.cast_nonneg K)))
  linarith [hminor ((1-δ)*x) ⟨hy0,hy1⟩]

end SatFinal.PolynomialLog
