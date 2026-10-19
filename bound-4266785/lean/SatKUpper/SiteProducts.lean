import SatKUpper.SiteGround
import SatUpper.PoissonPair

/-! The site endpoint needs only products of no-warning probabilities.
Evaluate their mixed moments directly on the original Poisson sites. -/

open MeasureTheory SatKUpper.Sampling SatKUpper.SiteVertex SatUpper
open SatUpper.PoissonConfiguration SatUpper.PoissonFunctional
open scoped NNReal

namespace SatKUpper.SiteProducts

variable {t r n : ℕ}

noncomputable def markLaw (law : CoinLaw t) (r : ℕ) : Measure (Mark t r) :=
  Measure.pi (fun _ => law.measure)

instance (law : CoinLaw t) (r : ℕ) : IsProbabilityMeasure (markLaw law r) := by
  unfold markLaw; infer_instance

variable (law : CoinLaw t)

noncomputable def test (a : Fin n × Bool) (x : Fresh t r n) : ℝ :=
  if (x 0).1 = a then mark law (fun j => (x j.succ).2) else 1

theorem test_bounds (a : Fin n × Bool) (x : Fresh t r n) :
    0 ≤ test law a x ∧ test law a x ≤ 1 := by
  unfold test
  split
  · exact mark_bounds law _
  · norm_num

theorem test_disjoint (v : Fin n) (x : Fresh t r n) :
    test law (v,true) x = 1 ∨ test law (v,false) x = 1 := by
  by_cases h : (x 0).1 = (v,true)
  · right
    simp [test, h]
  · left
    simp [test, h]

variable [NeZero n]

theorem projection_law :
    Measure.map (fun x : Fresh t r n => ((x 0).1, fun j : Fin r => (x j.succ).2))
      (freshLaw law r n) = (SatUpper.DirectFinite.uniform (Fin n × Bool)).prod (markLaw law r) := by
  have hs := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (r+1) => seedLaw law n) 0).map_eq
  have he : Measure.map (fun x : Fresh t r n => ((x 0).1, fun j : Fin r => (x j.succ).2))
      (freshLaw law r n) = Measure.map
        (Prod.map Prod.fst (fun x : Fin r → Seed t n => fun j => (x j).2))
        ((seedLaw law n).prod (Measure.pi (fun _ : Fin r => seedLaw law n))) := by
    rw [← hs, Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [he, ← Measure.map_prod_map _ _ measurable_fst (by fun_prop)]
  have hp : Measure.map (fun x : Fin r → Seed t n => fun j => (x j).2)
      (Measure.pi (fun _ => seedLaw law n)) = markLaw law r := by
    rw [Measure.pi_map_pi (fun _ => measurable_snd.aemeasurable)]
    simp [seedLaw, markLaw]
  rw [hp]
  simp [seedLaw]

theorem integral_test (a : Fin n × Bool) (F : ℝ → ℝ) (hF : F 1 = 1) :
    (∫ x, F (test law a x) ∂freshLaw law r n) =
      1 + ((∫ z, F (mark law z) ∂markLaw law r)-1)/(2*n) := by
  have he : (fun x : Fresh t r n => F (test law a x)) =
      (fun z : (Fin n × Bool) × Mark t r => if z.1 = a then F (mark law z.2) else 1) ∘
        (fun x => ((x 0).1, fun j : Fin r => (x j.succ).2)) := by
    funext x
    simp only [Function.comp_apply, test]
    split <;> simp_all
  rw [he]
  change (∫ x, (if (x 0).1 = a then F (mark law (fun j => (x j.succ).2)) else 1) ∂freshLaw law r n) = _
  rw [← integral_map (measurable_of_countable
    (fun x : Fresh t r n => ((x 0).1, fun j : Fin r => (x j.succ).2))).aemeasurable
    (measurable_of_countable (fun z : (Fin n × Bool) × Mark t r =>
      if z.1 = a then F (mark law z.2) else 1)).aestronglyMeasurable, projection_law law,
    integral_prod _ Integrable.of_finite]
  have hi (b : Fin n × Bool) :
      (∫ z, (if b = a then F (mark law z) else 1) ∂markLaw law r) =
        1 + Set.indicator {a} (fun _ : Fin n × Bool => (∫ z, F (mark law z) ∂markLaw law r)-1) b := by
    by_cases h : b = a <;> simp [h]
  simp_rw [hi]
  rw [integral_add (integrable_const _) Integrable.of_finite,
    integral_const, measureReal_univ_eq_one, one_smul,
    integral_indicator_const _ (measurableSet_singleton _)]
  rw [DirectProduct.uniform_eq_count]
  simp [measureReal_def, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_inv,
    div_eq_mul_inv, mul_comm]

noncomputable def side (a : Fin n × Bool) : Configuration (Fresh t r n) → ℝ := productTest (test law a)

omit [NeZero n] in
theorem side_bounds (a : Fin n × Bool) (c : Configuration (Fresh t r n)) :
    0 ≤ side law a c ∧ side law a c ≤ 1 :=
  productTest_bounds (fun x => (test_bounds law a x).1) (fun x => (test_bounds law a x).2) c

noncomputable def poissonMoment (r : ℕ) (a : ℝ) (j : ℕ) : ℝ :=
  Real.exp (a * ((∫ z, mark law z ^ j ∂markLaw law r)-1))

noncomputable def complementMoment (r : ℕ) (a : ℝ) (h : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (h+1), (-1 : ℝ)^j * (Nat.choose h j : ℝ) * poissonMoment law r a j

theorem mixed_moment (q : ℝ≥0)
    (v : Fin n) (j k : ℕ) :
    (∫ c, side law (v,true) c ^ j * side law (v,false) c ^ k ∂poisson q (freshLaw law r n)) =
      poissonMoment law r ((q : ℝ)/(2*n)) j * poissonMoment law r ((q : ℝ)/(2*n)) k := by
  rw [side, side, PoissonPair.mixed_moment q (freshLaw law r n)
    (fun x => (test_bounds law (v,true) x).1) (fun x => (test_bounds law (v,true) x).2)
    (fun x => (test_bounds law (v,false) x).1) (fun x => (test_bounds law (v,false) x).2) (test_disjoint law v)]
  rw [integral_test law _ (fun z => z ^ j) (one_pow j),
    integral_test law _ (fun z => z ^ k) (one_pow k)]
  congr 1 <;> congr 1 <;> simp only [add_sub_cancel_left] <;> ring

theorem integrable_complement (q : ℝ≥0) (v : Fin n) (k : ℕ) :
    Integrable (fun c => ((1-side law (v,true) c)*(1-side law (v,false) c))^k) (poisson q (freshLaw law r n)) := by
  apply ReplicaMoments.integrable_unit_interval _
    (((measurable_const.sub (measurable_productTest (measurable_of_countable _))).mul
      (measurable_const.sub (measurable_productTest (measurable_of_countable _)))).pow_const k)
  · intro c
    exact pow_nonneg (mul_nonneg (sub_nonneg.mpr (side_bounds law _ c).2) (sub_nonneg.mpr (side_bounds law _ c).2)) k
  · intro c
    have hA := side_bounds law (v,true) c
    have hB := side_bounds law (v,false) c
    dsimp only [side] at hA hB
    apply pow_le_one₀ (mul_nonneg (by linarith) (by linarith))
    exact mul_le_one₀ (by linarith) (by linarith) (by linarith)

noncomputable def upper (K : ℕ) (δ : ℝ) (v : Fin n) (c : Configuration (Fresh t r n)) : ℝ :=
  PoissonPair.majorant K δ (side law (v,true) c) (side law (v,false) c)

theorem integrable_upper (q : ℝ≥0) (K : ℕ) (δ : ℝ) (v : Fin n) :
    Integrable (upper law K δ v) (poisson q (freshLaw law r n)) := by
  simpa only [upper, PoissonPair.majorant] using
    (integrable_finset_sum (Finset.range K) (fun k _ =>
      (integrable_complement (r := r) law q v (k+1)).div_const (k+1 : ℝ))).neg.add
      (integrable_const (K*δ))

theorem integral_upper (q : ℝ≥0)
    (K : ℕ) (δ : ℝ) (v : Fin n) :
    (∫ c, upper law K δ v c ∂poisson q (freshLaw law r n)) =
      -(∑ h ∈ Finset.range K, (complementMoment law r ((q : ℝ)/(2*n)) (h+1))^2/(h+1)) +
        K*δ := by
  have he (k : ℕ) :
      (∫ c, ((1-side law (v,true) c)*(1-side law (v,false) c))^k ∂poisson q (freshLaw law r n)) =
        (complementMoment law r ((q : ℝ)/(2*n)) k)^2 :=
    PoissonPair.complement_moment _ (measurable_productTest (measurable_of_countable _))
      (measurable_productTest (measurable_of_countable _))
      (fun c => (side_bounds law _ c).1) (fun c => (side_bounds law _ c).2)
      (fun c => (side_bounds law _ c).1) (fun c => (side_bounds law _ c).2)
      (poissonMoment law r ((q : ℝ)/(2*n))) (mixed_moment law q v) k
  unfold upper PoissonPair.majorant
  have hi := integral_add (integrable_finset_sum (Finset.range K) (fun k _ =>
    (integrable_complement (r := r) law q v (k+1)).div_const (k+1 : ℝ))).neg (integrable_const (K*δ))
  simp only [Pi.neg_apply] at hi
  rw [hi,
    integral_neg, integral_finset_sum _ (fun k _ => (integrable_complement (r := r) law q v (k+1)).div_const (k+1 : ℝ)),
    integral_const, measureReal_univ_eq_one, one_smul]
  simp_rw [integral_div, he]

end SatKUpper.SiteProducts
