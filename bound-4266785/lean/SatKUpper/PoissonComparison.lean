import SatKUpper.BinomialPoisson
import SatUpper.Direct.Poisson

/-! Convert a local comparison at arity r+1 into the Poisson endpoint comparison.
This theorem is independent of the particular clause and site model. -/

open MeasureTheory
open scoped NNReal
open SatUpper SatUpper.DirectPoisson

namespace SatKUpper.PoissonComparison

theorem comparison (r : ℕ) {f : ℕ → ℕ → ℝ} {C d : ℝ}
    (hC : ∀ K L, ‖f (K+1) L-f K L‖ ≤ C)
    (hS : ∀ K L, ‖f K (L+1)-f K L‖ ≤ C)
    (h : ∀ K L, f (K+1) L-f K L -
      (r+1 : ℝ)*(f K (L+1)-f K L) + (r : ℝ)*d ≤ 0)
    (a : ℝ≥0) :
    expectation f a 0 ≤ expectation f 0 ((r+1)*a) - (r : ℝ)*a*d := by
  have hr : (r : ℝ)+1 ≠ 0 := by positivity
  have hd : ((r : ℝ)+1)*((r : ℝ)*d/((r : ℝ)+1)) = (r : ℝ)*d := by
    field_simp
  have hc := SatKUpper.BinomialPoisson.comparison (w := (r : ℝ)) (by positivity)
    hC hS (d := (r : ℝ)*d/((r : ℝ)+1)) (fun K L => by
      rw [hd]
      linarith [h K L]) a
  have he : ((r : ℝ)+1)*(a : ℝ)*((r : ℝ)*d/((r : ℝ)+1)) = (r : ℝ)*a*d := by
    field_simp
  rw [he] at hc
  have hgC := PoissonExpectation.linear_growth_of_bounded_increments
    (f := fun K => f K 0) (fun K => hC K 0)
  have hgS := PoissonExpectation.linear_growth_of_bounded_increments (hS 0)
  have hs := PoissonExpectation.poissonExpectation_eq_integral hgS ((r+1)*a)
  simp only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one] at hs
  rw [PoissonExpectation.poissonExpectation_eq_integral hgC a, hs] at hc
  simpa only [expectation, zero_law, integral_dirac] using hc

end SatKUpper.PoissonComparison
