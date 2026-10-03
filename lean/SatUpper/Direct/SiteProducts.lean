import SatUpper.Ground.Site
import SatUpper.PoissonPair

/-! The site endpoint needs only products of no-warning probabilities.
Evaluate their mixed moments directly on the original Poisson sites. -/

open MeasureTheory SatUpper.DirectFinite SatUpper.WitnessVertex
open SatUpper.PoissonConfiguration SatUpper.PoissonFunctional
open scoped NNReal

namespace SatUpper.DirectSiteProducts

variable {n : ℕ}

def test (a : Fin n × Bool) (x : Fresh n) : ℝ :=
  if (x 0).1 = a then mark ((x 1).2,(x 2).2) else 1

theorem test_bounds (a : Fin n × Bool) (x : Fresh n) :
    0 ≤ test a x ∧ test a x ≤ 1 := by
  unfold test
  split
  · exact mark_bounds _
  · norm_num

theorem test_disjoint (v : Fin n) (x : Fresh n) :
    test (v,true) x = 1 ∨ test (v,false) x = 1 := by
  by_cases h : (x 0).1 = (v,true)
  · right
    simp [test, h]
  · left
    simp [test, h]

variable [NeZero n]

theorem projection_law :
    Measure.map (fun x : Fresh n => ((x 0).1,((x 1).2,(x 2).2))) (freshLaw n) =
      (uniform (Fin n × Bool)).prod markLaw := by
  have h : Measure.map (fun x : Fresh n => ((x 0).1,((x 1).2,(x 2).2))) (freshLaw n) =
      Measure.map (Prod.map Prod.fst (Prod.map Prod.snd Prod.snd))
        ((seedLaw n).prod ((seedLaw n).prod (seedLaw n))) := by
    rw [← DirectProduct.triple_law (fun _ : Fin 3 => seedLaw n),
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [h, ← Measure.map_prod_map _ _ measurable_fst (measurable_snd.prodMap measurable_snd),
    ← Measure.map_prod_map _ _ measurable_snd measurable_snd]
  simp only [seedLaw, Measure.map_fst_prod, Measure.map_snd_prod, measure_univ, one_smul]
  congr 1
  apply Measure.ext_of_singleton
  intro x
  rw [← Set.singleton_prod_singleton, Measure.prod_prod]
  norm_num [DirectProduct.uniform_eq_count, markLaw, Measure.smul_apply, smul_eq_mul]
  rw [← ENNReal.mul_inv] <;> norm_num

theorem integral_test (a : Fin n × Bool) (F : ℝ → ℝ) (hF : F 1 = 1) :
    (∫ x, F (test a x) ∂freshLaw n) =
      1 + ((∫ z, F (mark z) ∂markLaw)-1)/(2*n) := by
  have he : (fun x : Fresh n => F (test a x)) =
      (fun z : (Fin n × Bool) × Mark => if z.1 = a then F (mark z.2) else 1) ∘
        (fun x => ((x 0).1,((x 1).2,(x 2).2))) := by
    funext x
    simp only [Function.comp_apply, test]
    split <;> simp_all
  rw [he]
  change (∫ x, (if (x 0).1 = a then F (mark ((x 1).2,(x 2).2)) else 1) ∂freshLaw n) = _
  rw [← integral_map (measurable_of_countable
    (fun x : Fresh n => ((x 0).1,((x 1).2,(x 2).2)))).aemeasurable
    (measurable_of_countable (fun z : (Fin n × Bool) × Mark =>
      if z.1 = a then F (mark z.2) else 1)).aestronglyMeasurable, projection_law,
    integral_prod _ Integrable.of_finite]
  have hi (b : Fin n × Bool) :
      (∫ z, (if b = a then F (mark z) else 1) ∂markLaw) =
        1 + Set.indicator {a} (fun _ : Fin n × Bool => (∫ z, F (mark z) ∂markLaw)-1) b := by
    by_cases h : b = a <;> simp [h]
  simp_rw [hi]
  rw [integral_add (integrable_const _) Integrable.of_finite,
    integral_const, measureReal_univ_eq_one, one_smul,
    integral_indicator_const _ (measurableSet_singleton _)]
  rw [DirectProduct.uniform_eq_count]
  simp [measureReal_def, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_inv,
    div_eq_mul_inv, mul_comm]

noncomputable def side (a : Fin n × Bool) : Configuration (Fresh n) → ℝ := productTest (test a)

omit [NeZero n] in
theorem side_bounds (a : Fin n × Bool) (c : Configuration (Fresh n)) :
    0 ≤ side a c ∧ side a c ≤ 1 :=
  productTest_bounds (fun x => (test_bounds a x).1) (fun x => (test_bounds a x).2) c

theorem mixed_moment (r : ℝ≥0) (hr : (r : ℝ)/(2*n) = 3*(Witness.alpha : ℝ)/2)
    (v : Fin n) (j k : ℕ) :
    (∫ c, side (v,true) c ^ j * side (v,false) c ^ k ∂poisson r (freshLaw n)) =
      Formalization.poissonProductMoment j * Formalization.poissonProductMoment k := by
  rw [side, side, PoissonPair.mixed_moment r (freshLaw n)
    (fun x => (test_bounds (v,true) x).1) (fun x => (test_bounds (v,true) x).2)
    (fun x => (test_bounds (v,false) x).1) (fun x => (test_bounds (v,false) x).2) (test_disjoint v)]
  rw [integral_test _ (fun z => z ^ j) (one_pow j), integral_test _ (fun z => z ^ k) (one_pow k),
    integral_mark_pow, integral_mark_pow]
  congr 1 <;> congr 1 <;> rw [add_sub_cancel_left, mul_div_assoc', ← div_mul_eq_mul_div, hr]

theorem integrable_complement (r : ℝ≥0) (v : Fin n) (k : ℕ) :
    Integrable (fun c => ((1-side (v,true) c)*(1-side (v,false) c))^k) (poisson r (freshLaw n)) := by
  apply ReplicaMoments.integrable_unit_interval _
    (((measurable_const.sub (measurable_productTest (measurable_of_countable _))).mul
      (measurable_const.sub (measurable_productTest (measurable_of_countable _)))).pow_const k)
  · intro c
    exact pow_nonneg (mul_nonneg (sub_nonneg.mpr (side_bounds _ c).2) (sub_nonneg.mpr (side_bounds _ c).2)) k
  · intro c
    have hA := side_bounds (v,true) c
    have hB := side_bounds (v,false) c
    dsimp only [side] at hA hB
    apply pow_le_one₀ (mul_nonneg (by linarith) (by linarith))
    exact mul_le_one₀ (by linarith) (by linarith) (by linarith)

noncomputable def upper (K : ℕ) (δ : ℝ) (v : Fin n) (c : Configuration (Fresh n)) : ℝ :=
  PoissonPair.majorant K δ (side (v,true) c) (side (v,false) c)

theorem integrable_upper (r : ℝ≥0) (K : ℕ) (δ : ℝ) (v : Fin n) :
    Integrable (upper K δ v) (poisson r (freshLaw n)) := by
  simpa only [upper, PoissonPair.majorant] using
    (integrable_finset_sum (Finset.range K) (fun k _ =>
      (integrable_complement r v (k+1)).div_const (k+1 : ℝ))).neg.add
      (integrable_const (K*δ))

theorem integral_upper (r : ℝ≥0) (hr : (r : ℝ)/(2*n) = 3*(Witness.alpha : ℝ)/2)
    (K : ℕ) (δ : ℝ) (v : Fin n) :
    (∫ c, upper K δ v c ∂poisson r (freshLaw n)) =
      negativeMomentSum K Formalization.noWarningMoment +
        K*δ := by
  have he (k : ℕ) :
      (∫ c, ((1-side (v,true) c)*(1-side (v,false) c))^k ∂poisson r (freshLaw n)) =
        (Formalization.noWarningMoment k)^2 :=
    PoissonPair.complement_moment _ (measurable_productTest (measurable_of_countable _))
      (measurable_productTest (measurable_of_countable _))
      (fun c => (side_bounds _ c).1) (fun c => (side_bounds _ c).2)
      (fun c => (side_bounds _ c).1) (fun c => (side_bounds _ c).2)
      Formalization.poissonProductMoment (mixed_moment r hr v) k
  unfold upper PoissonPair.majorant
  have hi := integral_add (integrable_finset_sum (Finset.range K) (fun k _ =>
    (integrable_complement r v (k+1)).div_const (k+1 : ℝ))).neg (integrable_const (K*δ))
  simp only [Pi.neg_apply] at hi
  rw [hi,
    integral_neg, integral_finset_sum _ (fun k _ => (integrable_complement r v (k+1)).div_const (k+1 : ℝ)),
    integral_const, measureReal_univ_eq_one, one_smul]
  simp_rw [integral_div, he]
  rfl

end SatUpper.DirectSiteProducts
