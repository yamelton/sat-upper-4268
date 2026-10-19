import SatUpper.PoissonFunctional
import SatUpper.PoissonExpectation

/-! Moment identities for products of marks in the actual Poisson configuration. -/

open MeasureTheory
open scoped NNReal
open SatUpper.PoissonConfiguration SatUpper.PoissonFunctional

namespace SatUpper.CompoundPoissonMoments

variable {α : Type*} [MeasurableSpace α]

theorem complement_pow_expansion (x : ℝ) (k : ℕ) :
    (1-x)^k = ∑ j ∈ Finset.range (k+1), (-1 : ℝ)^j * (Nat.choose k j : ℝ) * x^j := by
  rw [show 1-x = -x+1 by ring, add_pow]
  apply Finset.sum_congr rfl
  intro j _
  rw [one_pow, mul_one, neg_eq_neg_one_mul, mul_pow]
  ring

theorem integrable_size (r : ℝ≥0) (ν : Measure α) [IsProbabilityMeasure ν] :
    Integrable (fun x : Configuration α => (x.1 : ℝ)) (poisson r ν) := by
  have h : Integrable (fun n : ℕ => (n : ℝ))
      (Measure.map Sigma.fst (poisson r ν)) := by
    rw [size_poisson]
    apply PoissonExpectation.integrable_poisson_of_linear_growth
      (A := 0) (B := 1)
    intro n
    simp
  exact h.comp_measurable measurable_size

end SatUpper.CompoundPoissonMoments
