import SatUpper.InterpolationLaw

/-! Uniform clauses sampled with replacement. -/

open MeasureTheory

namespace SatUpper.ClauseEndpoint

abbrev Clause (n : ℕ) := Fin 3 → Fin n × Bool

noncomputable def clauseLaw (n : ℕ) : Measure (Clause n) :=
  Measure.pi (fun _ : Fin 3 => InterpolationLaw.signedVariableLaw n)

end SatUpper.ClauseEndpoint
