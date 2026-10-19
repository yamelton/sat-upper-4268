import SatFinal.PolynomialNumerics.Endpoint
import Mathlib.Algebra.Order.Floor.Semifield

namespace SatFinal

theorem clause_count (n : ℕ) :
    ⌊(853357 / 200000 : ℝ)*(n : ℝ)⌋₊ = 853357*n/200000 := by
  rw [div_mul_eq_mul_div, Nat.floor_div_ofNat]
  norm_cast
  rw [Nat.floor_natCast]

theorem satisfiabilityProbability_tendsto_zero : Filter.Tendsto
    (fun n : ℕ => SatKUpper.Model.satisfiabilityProbability 3 n (853357*n/200000))
    Filter.atTop (nhds 0) := by
  have h := SatFinal.Numerics.upperBound_4266785
  unfold SatKUpper.Model.UpperBound at h
  simpa only [clause_count] using h

end SatFinal
