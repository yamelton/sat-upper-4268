import SatUpper.Ground.Insertion

/-! Average the energetic correction over the finite warning-rate distribution. -/

open MeasureTheory SatUpper.DirectFinite SatUpper.GroundInsertion

namespace SatUpper.GroundEdge

theorem survey_law (n : ℕ) [NeZero n] :
    Measure.map (fun x : Fresh n => fun j => (x j).2) (freshLaw n) =
      Measure.pi (fun _ : Fin 3 => uniform (Fin 4)) := by
  unfold freshLaw
  rw [Measure.pi_map_pi (fun _ => measurable_snd.aemeasurable)]
  simp only [seedLaw, Measure.map_snd_prod, measure_univ, one_smul]

theorem average (n : ℕ) [NeZero n] (f : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∫ x : Fresh n, f (x 0).2 (x 1).2 (x 2).2 ∂freshLaw n) =
      (∑ i, ∑ j, ∑ k, f i j k)/64 := by
  have he : (∫ q : Fin 3 → Fin 4, f (q 0) (q 1) (q 2)
      ∂Measure.pi (fun _ => uniform (Fin 4))) =
      ∫ z : Fin 4 × (Fin 4 × Fin 4), f z.1 z.2.1 z.2.2
        ∂(uniform (Fin 4)).prod ((uniform (Fin 4)).prod (uniform (Fin 4))) := by
    rw [← DirectProduct.triple_law (fun _ : Fin 3 => uniform (Fin 4)),
      integral_map (by fun_prop) (measurable_of_countable _).aestronglyMeasurable]
  have hf : (∫ x : Fresh n, f (x 0).2 (x 1).2 (x 2).2 ∂freshLaw n) =
      ∫ q : Fin 3 → Fin 4, f (q 0) (q 1) (q 2)
        ∂Measure.pi (fun _ => uniform (Fin 4)) := by
    rw [← survey_law n, integral_map (measurable_of_countable _).aemeasurable
      (measurable_of_countable _).aestronglyMeasurable]
  rw [hf, he, integral_prod _ Integrable.of_finite]
  simp_rw [integral_prod _ Integrable.of_finite, integral_uniform, Fintype.card_fin,
    ← Finset.sum_div]
  ring

theorem correction_bound (n : ℕ) [NeZero n] (y : ℝ) :
    -2*(Witness.alpha : ℝ)*edgeMean n y ≤ Formalization.edgeCorrection := by
  have h (i j k : Fin 4) :
      Real.log (1-(Formalization.badMass i : ℝ)*Formalization.badMass j*Formalization.badMass k) ≤
      Real.log (1-(1-Real.exp (-y))*((Formalization.badMass i : ℝ)*Formalization.badMass j*Formalization.badMass k)) := by
    have hi := TrialFields.badMass_bounds i
    have hj := TrialFields.badMass_bounds j
    have hk := TrialFields.badMass_bounds k
    have h₀ := mul_nonneg hi.1 hj.1
    have h₁ := mul_le_mul_of_nonneg_left hj.2.le hi.1
    have h₂ := mul_le_mul_of_nonneg_left hk.2.le h₀
    have hp : 0 < 1-(Formalization.badMass i : ℝ)*Formalization.badMass j*Formalization.badMass k := by nlinarith
    apply Real.log_le_log hp
    nlinarith [mul_nonneg (Real.exp_pos (-y)).le (mul_nonneg h₀ hk.1)]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
      Finset.sum_le_sum (s := Finset.univ) (fun k _ => h i j k)))
  unfold edgeMean
  simp_rw [Fin.prod_univ_three]
  rw [average n (fun i j k => Real.log (1-(1-Real.exp (-y))*
    ((Formalization.badMass i : ℝ)*Formalization.badMass j*Formalization.badMass k)))]
  exact mul_le_mul_of_nonpos_left (div_le_div_of_nonneg_right hs (by norm_num))
    (by norm_num [Witness.alpha])

end SatUpper.GroundEdge
