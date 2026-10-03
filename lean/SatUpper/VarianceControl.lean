import SatUpper.FiniteVariance
import SatUpper.Obligations

/-! Minimum energy has one-clause Lipschitz constant one, hence linear variance. -/

namespace SatUpper.Formalization

theorem energy_variance_le (n M : ℕ) [NeZero n] : GroundFormula.variance n M ≤ M := by
  simpa [GroundFormula.variance] using FiniteVariance.variance_fin_pi_le M
    (fun F : GroundFormula.Formula n M => (GroundFormula.energy F : ℝ))
    (by norm_num : (0 : ℝ) ≤ 1) GroundFormula.energy_one_clause_lipschitz

theorem linearVarianceControl : LinearVarianceControl := by
  refine ⟨Witness.alpha, by norm_num [Witness.alpha], ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  letI : NeZero n := ⟨by omega⟩
  exact (energy_variance_le n (clauseCount n)).trans (clauseCount_le_alpha_mul n)

/-- Only the analytic comparison and numerical enclosure remain as hypotheses. -/
theorem upperBound_of_comparison_and_enclosure
    (hcomparison : AsymptoticComparison) (hnumerical : NumericalEnclosure) : CandidateUpperBound :=
  upperBound_of_obligations hcomparison hnumerical linearVarianceControl

end SatUpper.Formalization
