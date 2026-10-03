import SatUpper.Local
import Mathlib.Algebra.Order.Floor.Ring

/-! Outward rounding of rational intervals. -/

namespace SatUpper.Enclosures

def lowerOnGrid (scale : ℕ) (x : ℚ) : ℚ :=
  (⌊x * (scale : ℚ)⌋ : ℚ) / (scale : ℚ)

def upperOnGrid (scale : ℕ) (x : ℚ) : ℚ := -lowerOnGrid scale (-x)

theorem lowerOnGrid_le {scale : ℕ} (hs : 0 < scale) (x : ℚ) :
    lowerOnGrid scale x ≤ x := by
  unfold lowerOnGrid
  apply (div_le_iff₀ (show (0 : ℚ) < scale by exact_mod_cast hs)).mpr
  exact Int.floor_le _

theorem le_upperOnGrid {scale : ℕ} (hs : 0 < scale) (x : ℚ) :
    x ≤ upperOnGrid scale x := by
  unfold upperOnGrid
  have h := lowerOnGrid_le hs (-x)
  linarith

theorem rounded_enclosure {scale : ℕ} (hs : 0 < scale)
    {l u : ℚ} {x : ℝ} (hl : (l : ℝ) ≤ x) (hu : x ≤ (u : ℝ)) :
    (lowerOnGrid scale l : ℝ) ≤ x ∧ x ≤ (upperOnGrid scale u : ℝ) := by
  have hl' : (lowerOnGrid scale l : ℝ) ≤ (l : ℝ) := by
    exact_mod_cast lowerOnGrid_le hs l
  have hu' : (u : ℝ) ≤ (upperOnGrid scale u : ℝ) := by
    exact_mod_cast le_upperOnGrid hs u
  exact ⟨hl'.trans hl, hu.trans hu'⟩

end SatUpper.Enclosures
