import SatUpper.LegalConditioning
import SatUpper.Series
import SatUpper.Witness

/-! The three ingredients assembled by the final theorem, proved in
`VarianceControl.lean`, `NumericalEnclosure.lean`, and `ModelTransfer.lean`. -/

namespace SatUpper.Formalization

def badMass (i : Fin 4) : ℚ :=
  match i.val with
  | 0 => 1 / 20
  | 1 => 17 / 20
  | _ => 2 / 5

def markMoment (j : ℕ) : ℚ :=
  (∑ i : Fin 4, ∑ k : Fin 4, (1 - badMass i * badMass k) ^ j) / 16

noncomputable def poissonProductMoment (j : ℕ) : ℝ :=
  Real.exp ((3 * (Witness.alpha : ℝ) / 2) * ((markMoment j : ℝ) - 1))

noncomputable def noWarningMoment (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1),
    (-1 : ℝ) ^ j * (Nat.choose k j : ℝ) * poissonProductMoment j

noncomputable def edgeCorrection : ℝ :=
  -2 * (Witness.alpha : ℝ) *
    ((∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4,
      Real.log (1 - (badMass i : ℝ) * (badMass j : ℝ) * (badMass k : ℝ))) / 64)

/-- The real-valued finite expression the Python certificate bounds. -/
noncomputable def finiteAnalyticBound : ℝ :=
  negativeMomentSum Witness.cutoff noWarningMoment + edgeCorrection

/-- Proved in `NumericalEnclosure.lean` by sound analytic enclosures and kernel arithmetic. -/
def NumericalEnclosure : Prop :=
  finiteAnalyticBound ≤ (Witness.roundedUpper : ℝ)

/-- Proved in `ModelTransfer.lean` by interpolation and transfer to legal clauses. -/
def AsymptoticComparison : Prop :=
  ∀ y : ℝ, 0 < y → ∀ δ : ℝ, 0 < δ → ∀ᶠ (n : ℕ) in Filter.atTop,
    (-y / n) * GroundFormula.mean n (clauseCount n) ≤
      finiteAnalyticBound + (Witness.cutoff : ℝ)*Real.exp (-y) + δ

/-- Proved in `VarianceControl.lean` from finite-product variance decomposition. -/
def LinearVarianceControl : Prop :=
  ∃ V : ℝ, 0 ≤ V ∧ ∀ᶠ (n : ℕ) in Filter.atTop,
    GroundFormula.variance n (clauseCount n) ≤ V * n

theorem clauseCount_le_alpha_mul (n : ℕ) :
    (clauseCount n : ℝ) ≤ (Witness.alpha : ℝ) * n := by
  have hh : clauseCount n * 250 ≤ 1067 * n := Nat.div_mul_le_self _ _
  have hr : (clauseCount n : ℝ) * 250 ≤ 1067 * (n : ℝ) := by exact_mod_cast hh
  norm_num [Witness.alpha]
  linarith

/-- Choose the softening parameter large enough, then use concentration.
No numerical temperature or fractional exponent is needed. -/
theorem upperBound_of_obligations
    (hcomparison : AsymptoticComparison)
    (hnumerical : NumericalEnclosure)
    (hvariance : LinearVarianceControl) : CandidateUpperBound := by
  obtain ⟨V, hV, hv⟩ := hvariance
  have hr : (Witness.roundedUpper : ℝ) < 0 := by exact_mod_cast Witness.roundedUpper_neg
  have hδ : 0 < -(Witness.roundedUpper : ℝ)/4 := by linarith
  have ht : Filter.Tendsto (fun y : ℝ => (Witness.cutoff : ℝ)*Real.exp (-y))
      Filter.atTop (nhds 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul (Witness.cutoff : ℝ)
  obtain ⟨y, hy, he⟩ := ((Filter.eventually_gt_atTop (0 : ℝ)).and
    (ht.eventually_le_const hδ)).exists
  let c : ℝ := -(Witness.roundedUpper : ℝ)/(2*y)
  have hc : 0 < c := div_pos (neg_pos.mpr hr) (mul_pos (by norm_num) hy)
  apply LegalConditioning.candidate_of_mean_and_variance_bounds
    Witness.alpha c V hc hV clauseCount_le_alpha_mul _ hv
  filter_upwards [hcomparison y hy _ hδ, Filter.eventually_ge_atTop 1] with n hn hnat
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  apply (mul_le_mul_iff_right₀ (div_pos hy hnpos)).mp
  calc
    (y/n)*(c*n) = -(Witness.roundedUpper : ℝ)/2 := by dsimp [c]; field_simp
    _ ≤ (y/n)*GroundFormula.mean n (clauseCount n) := by
      have hb := hnumerical
      unfold NumericalEnclosure at hb
      rw [neg_div, neg_mul] at hn
      linarith

end SatUpper.Formalization
