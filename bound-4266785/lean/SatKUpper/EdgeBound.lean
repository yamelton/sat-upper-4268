import SatKUpper.SiteProducts
import SatKUpper.LocalComparison

/-! The hard edge correction is independent of the variable count and
dominates the softened correction at every positive inverse temperature. -/

open MeasureTheory SatKUpper.Sampling SatKUpper.SiteVertex SatKUpper.SiteProducts

namespace SatKUpper.EdgeBound

variable {t r n : ℕ} (law : CoinLaw t)

theorem product_bounds (z : Mark t (r+1)) :
    0 ≤ ∏ j, law.rate (z j) ∧ (∏ j, law.rate (z j)) < 1 := by
  refine ⟨Finset.prod_nonneg (fun j _ => law.nonneg (z j)), ?_⟩
  rw [Fin.prod_univ_succ]
  have h := Finset.prod_le_one (s := (Finset.univ : Finset (Fin r)))
    (fun j _ => law.nonneg (z j.succ)) (fun j _ => (law.lt_one (z j.succ)).le)
  exact (mul_le_of_le_one_right (law.nonneg (z 0)) h).trans_lt (law.lt_one (z 0))

noncomputable def correction (r : ℕ) : ℝ :=
  -(∫ z, Real.log (1-∏ j, law.rate (z j)) ∂markLaw law (r+1))

theorem marks_law [NeZero n] :
    Measure.map (fun x : Fresh t r n => fun j => (x j).2) (freshLaw law r n) =
      markLaw law (r+1) := by
  unfold freshLaw
  rw [Measure.pi_map_pi (fun _ => measurable_snd.aemeasurable)]
  simp [seedLaw, markLaw]

theorem edge_le [NeZero n] (y : ℝ) :
    -correction law r ≤ LocalComparison.edgeMean law r n y := by
  have h (z : Mark t (r+1)) :
      Real.log (1-∏ j, law.rate (z j)) ≤
        Real.log (1-(1-Real.exp (-y))*∏ j, law.rate (z j)) := by
    have hb := product_bounds law z
    apply Real.log_le_log (sub_pos.mpr hb.2)
    nlinarith [mul_nonneg (Real.exp_pos (-y)).le hb.1]
  have he := integral_mono (μ := markLaw law (r+1))
    Integrable.of_finite Integrable.of_finite h
  rw [← marks_law (n := n) law,
    integral_map (measurable_of_countable _).aemeasurable
      (measurable_of_countable _).aestronglyMeasurable] at he
  simpa only [correction, neg_neg, LocalComparison.edgeMean,
    ← marks_law (n := n) law,
    integral_map (measurable_of_countable _).aemeasurable
      (measurable_of_countable _).aestronglyMeasurable] using he

end SatKUpper.EdgeBound
