import SatUpper.Local
import Mathlib.Tactic.FinCases

/-! Paired warning rates in twentieths, inherited from the two-survey witness.
The four equally likely labels use the pairs below; the repeated rate 2/5
has total probability 1/2. Inner warnings now use a Bernoulli law.
`NumericalEnclosure.lean` certifies the resulting finite expression. -/

namespace SatUpper.Witness

def alpha : ℚ := 1067 / 250
def cutoff : ℕ := 128

def survey (i : Fin 2) : ℚ × ℚ :=
  if i = 0 then (1 / 20, 17 / 20) else (2 / 5, 2 / 5)

theorem survey_admissible (i : Fin 2) :
    0 ≤ (survey i).1 ∧ 0 ≤ (survey i).2 ∧
    (survey i).1 + (survey i).2 ≤ 1 ∧
    (survey i).1 < 1 ∧ (survey i).2 < 1 := by
  fin_cases i <;> norm_num [survey]

def roundedUpper : ℚ := -1 / 10 ^ 5

theorem roundedUpper_neg : roundedUpper < 0 := by
  norm_num [roundedUpper]

end SatUpper.Witness
