import SatUpper.GridExponential
import SatUpper.VertexEnclosures

/-! A uniform exponential enclosure, computed entirely inside Lean.
The finite list shares the computation across moments; it contains no
externally generated numerical data. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace SatUpper.NumericalMoments

def argument (j : ℕ) : ℚ :=
  (3 * Witness.alpha / 2) * (Formalization.markMoment j - 1)

def bounds (j : ℕ) : ℚ × ℚ :=
  let b := GridExponential.bounds (2^320) 160 (argument j)
  (Enclosures.lowerOnGrid (2^160) b.1, Enclosures.upperOnGrid (2^160) b.2)

def table : List (ℚ × ℚ) := (List.range (Witness.cutoff + 1)).map bounds

def lower (j : ℕ) : ℚ := (table.getD j (0, 0)).1

def upper (j : ℕ) : ℚ := (table.getD j (0, 0)).2

/-- The elementary reciprocal bound is valid at every scaled argument. -/
theorem checked : ∀ j : Fin (Witness.cutoff + 1),
    argument j < (2 : ℚ)^160 := by
  decide +kernel

theorem enclosures (j : ℕ) (hj : j ≤ Witness.cutoff) :
    (lower j : ℝ) ≤ Formalization.poissonProductMoment j ∧
    Formalization.poissonProductMoment j ≤ (upper j : ℝ) := by
  have ht : table.getD j (0, 0) = bounds j := by
    simp [table, List.getD, List.getElem?_range (Nat.lt_succ_of_le hj)]
  have hb := GridExponential.bounds_correct (scale := 2^320) (by norm_num) 160 (argument j) (checked ⟨j, Nat.lt_succ_of_le hj⟩)
  have hr := Enclosures.rounded_enclosure (scale := 2^160) (by norm_num) hb.1 hb.2
  simpa only [lower, upper, ht, bounds, argument, Formalization.poissonProductMoment,
    Rat.cast_mul, Rat.cast_div, Rat.cast_sub, Rat.cast_one, Rat.cast_ofNat] using hr

end SatUpper.NumericalMoments
