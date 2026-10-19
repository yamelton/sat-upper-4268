import SatUpper.Local
import Mathlib.Tactic.FinCases

/-! Three switch rates represented by eight equally likely labels. -/

namespace SatUpper.Witness

def alpha : ℚ := 4267 / 1000
def cutoff : ℕ := 256

def roundedUpper : ℚ := -1 / 125000

theorem roundedUpper_neg : roundedUpper < 0 := by
  norm_num [roundedUpper]

end SatUpper.Witness
