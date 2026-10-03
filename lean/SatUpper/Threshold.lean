import SatUpper.ModelTransfer

/-! Unconditional upper bound at density 1067/250 for the stated random 3-SAT model. -/

namespace SatUpper

/-- Random legal 3-SAT with floor((1067/250)*n) iid clauses is unsatisfiable
with probability tending to one as n tends to infinity. -/
theorem upperBound_4268 : CandidateUpperBound :=
  Formalization.upperBound_of_comparison ModelTransfer.asymptoticComparison

/-- The same theorem with the target probability and exact clause count exposed. -/
theorem satisfiabilityProbability_4268_tendsto_zero :
    Filter.Tendsto
      (fun n : ℕ => satisfiabilityProbability n (1067*n/250))
      Filter.atTop (nhds 0) :=
  upperBound_4268

end SatUpper
