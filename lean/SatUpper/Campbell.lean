import SatUpper.PoissonConfiguration
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-! The first moment of the Poisson distribution. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace SatUpper.Campbell

theorem poisson_weight_succ (r : ℝ≥0) (n : ℕ) :
    poissonPMFReal r (n + 1) * (n + 1 : ℝ) = (r : ℝ) * poissonPMFReal r n := by
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hfact : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  simp only [poissonPMFReal, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, pow_succ]
  field_simp

theorem poisson_mean_series (r : ℝ≥0) :
    HasSum (fun n => poissonPMFReal r n * (n : ℝ)) (r : ℝ) := by
  apply (hasSum_nat_add_iff' 1).mp
  simp only [Finset.sum_range_one, Nat.cast_zero, mul_zero, sub_zero, Nat.cast_add, Nat.cast_one]
  simp_rw [poisson_weight_succ]
  simpa using (poissonPMFRealSum r).mul_left (r : ℝ)

end SatUpper.Campbell
