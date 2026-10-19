import SatKUpper.Model
import SatUpper.FiniteVariance

/-! Uniform variance control for the actual k-SAT minimum violation count. -/

namespace SatKUpper.Variance

theorem energy_variance_le (k n M : ℕ) [NeZero n] : Model.variance k n M ≤ M := by
  simpa [Model.variance] using SatUpper.FiniteVariance.variance_fin_pi_le M
    (fun F : Model.Formula k n M => (Model.energy F : ℝ))
    (by norm_num : (0 : ℝ) ≤ 1) Model.energy_one_clause_lipschitz

end SatKUpper.Variance
