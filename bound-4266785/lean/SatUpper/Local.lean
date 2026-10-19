import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Elementary inequalities used by the candidate interpolation argument.
These theorems do not establish the probabilistic interpolation inequality. -/

namespace SatUpper

theorem cubic_identity (B C : ℝ) :
    B ^ 3 - 3 * B * C ^ 2 + 2 * C ^ 3 = (B - C) ^ 2 * (B + 2 * C) := by
  ring

theorem cubic_nonneg {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) :
    0 ≤ B ^ 3 - 3 * B * C ^ 2 + 2 * C ^ 3 := by
  rw [cubic_identity]
  exact mul_nonneg (sq_nonneg _) (by positivity)

def noConflict (A B : ℝ) : ℝ := A + B - A * B

theorem noConflict_complement (A B : ℝ) :
    noConflict A B = 1 - (1 - A) * (1 - B) := by
  unfold noConflict
  ring

theorem factor_bounds {t : ℝ} (ht1 : t ≤ 1) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    t ≤ 1-(1-t)*z ∧ 1-(1-t)*z ≤ 1 := by
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr ht1) hz0,
    mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hz1)]

end SatUpper
