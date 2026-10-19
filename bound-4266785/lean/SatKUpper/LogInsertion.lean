import SatUpper.LogInsertion
import SatKUpper.ReplicaPower

/-! Local logarithmic insertion comparison for every positive clause size.
The random formula endpoint and numerical certificates are separate obligations. -/

open MeasureTheory SatUpper.LogInsertion SatKUpper.ReplicaPower

namespace SatKUpper.LogInsertion

variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]

theorem power_log_insertion_nonpos (ν : Measure Ξ) (μ : Measure Ω)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure μ] (n : ℕ)
    {b c : Ξ → Ω → ℝ} (hb : Measurable (Function.uncurry b))
    (hc : Measurable (Function.uncurry c))
    (hb0 : ∀ x ω, 0 ≤ b x ω) (hb1 : ∀ x ω, b x ω ≤ 1)
    (hc0 : ∀ x ω, 0 ≤ c x ω) (hc1 : ∀ x ω, c x ω ≤ 1)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    insertionLog ν μ q (n + 1) (fun _ => b) -
      (n + 1 : ℝ)*insertionLog ν μ q (n + 1) (mixedFamily n b c) +
      (n : ℝ)*insertionLog ν μ q (n + 1) (fun _ => c) ≤ 0 := by
  have hf (j : Fin (n + 1)) : Measurable (Function.uncurry (mixedFamily n b c j)) := by
    by_cases hj : j.val = 0 <;> simp only [mixedFamily, hj, ite_true, ite_false] <;> assumption
  have h0 (j : Fin (n + 1)) (x : Ξ) (ω : Ω) : 0 ≤ mixedFamily n b c j x ω := by
    by_cases hj : j.val = 0 <;> simp only [mixedFamily, hj, ite_true, ite_false]
    · exact hb0 x ω
    · exact hc0 x ω
  have h1 (j : Fin (n + 1)) (x : Ξ) (ω : Ω) : mixedFamily n b c j x ω ≤ 1 := by
    by_cases hj : j.val = 0 <;> simp only [mixedFamily, hj, ite_true, ite_false]
    · exact hb1 x ω
    · exact hc1 x ω
  have hB := insertionLog_hasSum ν μ (n + 1) (fun _ => hb) (fun _ => hb0) (fun _ => hb1) hq0 hq1
  have hM := insertionLog_hasSum ν μ (n + 1) hf h0 h1 hq0 hq1
  have hC := insertionLog_hasSum ν μ (n + 1) (fun _ => hc) (fun _ => hc0) (fun _ => hc1) hq0 hq1
  rw [← ((hB.sub (hM.mul_left (n + 1 : ℝ))).add (hC.mul_left (n : ℝ))).tsum_eq]
  apply tsum_nonpos
  intro r
  have h := power_moment_nonneg ν μ n (r+1) hb hc hb0 hb1 hc0 hc1
  have ha : 0 ≤ q^(r+1)/((r : ℝ)+1) := by positivity
  nlinarith [mul_nonneg ha h]

end SatKUpper.LogInsertion
