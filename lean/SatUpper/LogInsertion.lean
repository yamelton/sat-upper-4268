import SatUpper.LogMomentSeries
import SatUpper.ReplicaCubic

/-! Averaged logarithmic insertion inequality with a shared replica environment.

The nonnegative cubic remainder is the arity-three instance of the polynomial
in Lelarge–Oulamara (30), https://arxiv.org/html/1708.02457v2. Nonnegative
features supply the odd-arity sign condition; the inequality is proved here.
-/

open MeasureTheory
open SatUpper.ReplicaMoments SatUpper.ReplicaCubic

namespace SatUpper.LogInsertion

variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]

noncomputable def meanProduct (μ : Measure Ω) (k : ℕ)
    (f : Fin k → Ξ → Ω → ℝ) (x : Fin k → Ξ) : ℝ :=
  ∫ ω, ∏ j, f j (x j) ω ∂μ

theorem measurable_meanProduct (μ : Measure Ω) [IsProbabilityMeasure μ]
    (k : ℕ) {f : Fin k → Ξ → Ω → ℝ}
    (hf : ∀ j, Measurable (Function.uncurry (f j))) :
    Measurable (meanProduct μ k f) := by
  have hm : Measurable (fun z : (Fin k → Ξ) × Ω => ∏ j, f j (z.1 j) z.2) := by
    apply Finset.measurable_prod
    intro j _
    have he : Measurable (fun z : (Fin k → Ξ) × Ω => (z.1 j, z.2)) :=
      ((measurable_pi_apply j).comp measurable_fst).prodMk measurable_snd
    exact (hf j).comp he
  exact hm.stronglyMeasurable.integral_prod_right.measurable

theorem meanProduct_bounds (μ : Measure Ω) [IsProbabilityMeasure μ]
    (k : ℕ) {f : Fin k → Ξ → Ω → ℝ}
    (hf : ∀ j, Measurable (Function.uncurry (f j)))
    (h0 : ∀ j x ω, 0 ≤ f j x ω) (h1 : ∀ j x ω, f j x ω ≤ 1)
    (x : Fin k → Ξ) : 0 ≤ meanProduct μ k f x ∧ meanProduct μ k f x ≤ 1 := by
  have hm : Measurable (fun ω => ∏ j, f j (x j) ω) := by
    apply Finset.measurable_prod
    intro j _
    exact (hf j).comp (measurable_const.prodMk measurable_id)
  have hp0 (ω : Ω) : 0 ≤ ∏ j, f j (x j) ω :=
    Finset.prod_nonneg (fun j _ => h0 j (x j) ω)
  have hp1 (ω : Ω) : (∏ j, f j (x j) ω) ≤ 1 :=
    Finset.prod_le_one (fun j _ => h0 j (x j) ω) (fun j _ => h1 j (x j) ω)
  refine ⟨integral_nonneg hp0, ?_⟩
  have hi := integrable_unit_interval μ hm hp0 hp1
  simpa only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul] using
    integral_mono hi (integrable_const (1 : ℝ)) hp1

noncomputable def insertionLog (ν : Measure Ξ) (μ : Measure Ω) (q : ℝ)
    (k : ℕ) (f : Fin k → Ξ → Ω → ℝ) : ℝ :=
  ∫ x, Real.log (1-q*meanProduct μ k f x) ∂Measure.pi (fun _ => ν)

theorem insertionLog_hasSum (ν : Measure Ξ) (μ : Measure Ω)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure μ] (k : ℕ)
    {f : Fin k → Ξ → Ω → ℝ} (hf : ∀ j, Measurable (Function.uncurry (f j)))
    (h0 : ∀ j x ω, 0 ≤ f j x ω) (h1 : ∀ j x ω, f j x ω ≤ 1)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun r : ℕ => -(q^(r+1)/(r+1))*productMoment ν μ k (r+1) f)
      (insertionLog ν μ q k f) := by
  have hb := meanProduct_bounds μ k hf h0 h1
  exact LogMomentSeries.hasSum_integral_log (Measure.pi (fun _ => ν))
    (measurable_meanProduct μ k hf) (fun x => (hb x).1) (fun x => (hb x).2) hq0 hq1

theorem cubic_log_insertion_nonpos (ν : Measure Ξ) (μ : Measure Ω)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {b c : Ξ → Ω → ℝ} (hb : Measurable (Function.uncurry b))
    (hc : Measurable (Function.uncurry c))
    (hb0 : ∀ x ω, 0 ≤ b x ω) (hb1 : ∀ x ω, b x ω ≤ 1)
    (hc0 : ∀ x ω, 0 ≤ c x ω) (hc1 : ∀ x ω, c x ω ≤ 1)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    insertionLog ν μ q 3 (fun _ => b) -
      3*insertionLog ν μ q 3 (mixedFamily b c) +
      2*insertionLog ν μ q 3 (fun _ => c) ≤ 0 := by
  have hf (j : Fin 3) : Measurable (Function.uncurry (mixedFamily b c j)) := by
    by_cases hj : j.val = 0 <;> simp only [mixedFamily, hj, ite_true, ite_false] <;> assumption
  have h0 (j : Fin 3) (x : Ξ) (ω : Ω) : 0 ≤ mixedFamily b c j x ω := by
    by_cases hj : j.val = 0 <;> simp only [mixedFamily, hj, ite_true, ite_false]
    · exact hb0 x ω
    · exact hc0 x ω
  have h1 (j : Fin 3) (x : Ξ) (ω : Ω) : mixedFamily b c j x ω ≤ 1 := by
    by_cases hj : j.val = 0 <;> simp only [mixedFamily, hj, ite_true, ite_false]
    · exact hb1 x ω
    · exact hc1 x ω
  have hB := insertionLog_hasSum ν μ 3 (fun _ => hb) (fun _ => hb0) (fun _ => hb1) hq0 hq1
  have hM := insertionLog_hasSum ν μ 3 hf h0 h1 hq0 hq1
  have hC := insertionLog_hasSum ν μ 3 (fun _ => hc) (fun _ => hc0) (fun _ => hc1) hq0 hq1
  rw [← ((hB.sub (hM.mul_left 3)).add (hC.mul_left 2)).tsum_eq]
  apply tsum_nonpos
  intro r
  have h := cubic_moment_nonneg ν μ (r+1) hb hc hb0 hb1 hc0 hc1
  have ha : 0 ≤ q^(r+1)/((r : ℝ)+1) := by positivity
  nlinarith [mul_nonneg ha h]

end SatUpper.LogInsertion
