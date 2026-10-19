import SatKUpper.Insertion

/-! The general logarithmic comparison applied to actual clause/site insertions. -/

open MeasureTheory SatKUpper.Sampling SatKUpper.Ground SatKUpper.Insertion

namespace SatKUpper.LocalComparison

theorem product_bounds {t r n L : ℕ} (f : Fin (r+1) → Seed t n → Fields r L → ℝ)
    (hb : ∀ j x a, 0 ≤ f j x a ∧ f j x a ≤ 1) (x : Fresh t r n) (a : Fields r L) :
    0 ≤ ∏ j, f j (x j) a ∧ (∏ j, f j (x j) a) ≤ 1 :=
  ⟨Finset.prod_nonneg (fun j _ => (hb j (x j) a).1),
    Finset.prod_le_one (fun j _ => (hb j (x j) a).1) (fun j _ => (hb j (x j) a).2)⟩

theorem mixed_bounds {t r n K L : ℕ} (law : CoinLaw t) (c : Fin K → Fresh t r n)
    (s : Fin L → Fresh t r n) (j : Fin (r+1)) (x : Seed t n) (a : Fields r L) :
    0 ≤ ReplicaPower.mixedFamily r (backbone c s) (rate law) j x a ∧
      ReplicaPower.mixedFamily r (backbone c s) (rate law) j x a ≤ 1 := by
  unfold ReplicaPower.mixedFamily
  split
  · exact backbone_bounds c s x a
  · exact rate_bounds law x a

theorem clause_increment {t r n K L : ℕ} (law : CoinLaw t) (y : ℝ)
    (c : Fin K → Fresh t r n) (s : Fin L → Fresh t r n) (x : Fresh t r n) :
    entropy law y (Fin.cons x c) s - entropy law y c s =
      Real.log (1-(1-Real.exp (-y))*SatUpper.LogInsertion.meanProduct (tilted law y c s)
        (r+1) (fun _ => backbone c s) x) := by
  have hb := product_bounds (fun _ => backbone c s) (fun _ => backbone_bounds c s) x
  exact log_ratio law y c s (fun a => (hb a).1) (fun a => (hb a).2)
    (moment_pos law y (Fin.cons x c) s) (by simp_rw [moment, clause_factor])

theorem site_increment {t r n K L : ℕ} (law : CoinLaw t) (y : ℝ)
    (c : Fin K → Fresh t r n) (s : Fin L → Fresh t r n) (x : Fresh t r n) :
    entropy law y c (Fin.cons x s) - entropy law y c s =
      Real.log (1-(1-Real.exp (-y))*SatUpper.LogInsertion.meanProduct (tilted law y c s)
        (r+1) (ReplicaPower.mixedFamily r (backbone c s) (rate law)) x) := by
  have hb := product_bounds _ (mixed_bounds law c s) x
  exact log_ratio law y c s (fun a => (hb a).1) (fun a => (hb a).2)
    (moment_pos law y c (Fin.cons x s)) (site_moment law y c s x)

noncomputable def edgeMean {t : ℕ} (law : CoinLaw t) (r n : ℕ) [NeZero n] (y : ℝ) : ℝ :=
  ∫ x : Fresh t r n, Real.log (1-(1-Real.exp (-y))*∏ j, law.rate (x j).2)
    ∂freshLaw law r n

theorem power_nonpos {t r n K L : ℕ} [NeZero n] (law : CoinLaw t) {y : ℝ} (hy : 0 ≤ y)
    (c : Fin K → Fresh t r n) (s : Fin L → Fresh t r n) :
    (∫ x, entropy law y (Fin.cons x c) s - entropy law y c s ∂freshLaw law r n) -
      (r+1 : ℝ)*(∫ x, entropy law y c (Fin.cons x s) - entropy law y c s ∂freshLaw law r n) +
      (r : ℝ)*edgeMean law r n y ≤ 0 := by
  have h := SatKUpper.LogInsertion.power_log_insertion_nonpos (seedLaw law n)
    (tilted law y c s) r (b := backbone c s) (c := rate law)
    (measurable_of_countable _) (measurable_of_countable _)
    (fun x a => (backbone_bounds c s x a).1) (fun x a => (backbone_bounds c s x a).2)
    (fun x a => (rate_bounds law x a).1) (fun x a => (rate_bounds law x a).2)
    (q := 1-Real.exp (-y)) (by linarith [Real.exp_le_one_iff.mpr (neg_nonpos.mpr hy)])
    (by linarith [Real.exp_pos (-y)])
  simp_rw [clause_increment, site_increment]
  simpa only [SatUpper.LogInsertion.insertionLog, SatUpper.LogInsertion.meanProduct,
    rate, integral_const, measureReal_univ_eq_one, one_smul, edgeMean, freshLaw] using h

theorem increment_bound {t r n K L : ℕ} (law : CoinLaw t) {y : ℝ} (hy : 0 ≤ y)
    (c : Fin K → Fresh t r n) (s : Fin L → Fresh t r n)
    (f : Fin (r+1) → Seed t n → Fields r L → ℝ)
    (hb : ∀ j x a, 0 ≤ f j x a ∧ f j x a ≤ 1) (x : Fresh t r n) :
    ‖Real.log (1-(1-Real.exp (-y))*SatUpper.LogInsertion.meanProduct
      (tilted law y c s) (r+1) f x)‖ ≤ y := by
  have hz := SatUpper.LogInsertion.meanProduct_bounds (tilted law y c s) (r+1)
    (fun _ => measurable_of_countable _)
    (fun j x a => (hb j x a).1) (fun j x a => (hb j x a).2) x
  have h := SatUpper.GroundFinite.log_factor_bounds hy hz.1 hz.2
  rw [Real.norm_eq_abs, abs_of_nonpos h.2]
  linarith [h.1]

theorem clause_increment_bound {t r n K L : ℕ} (law : CoinLaw t) {y : ℝ} (hy : 0 ≤ y)
    (c : Fin K → Fresh t r n) (s : Fin L → Fresh t r n) (x : Fresh t r n) :
    ‖entropy law y (Fin.cons x c) s - entropy law y c s‖ ≤ y := by
  rw [clause_increment]
  exact increment_bound law hy c s _ (fun _ => backbone_bounds c s) x

theorem site_increment_bound {t r n K L : ℕ} (law : CoinLaw t) {y : ℝ} (hy : 0 ≤ y)
    (c : Fin K → Fresh t r n) (s : Fin L → Fresh t r n) (x : Fresh t r n) :
    ‖entropy law y c (Fin.cons x s) - entropy law y c s‖ ≤ y := by
  rw [site_increment]
  exact increment_bound law hy c s _ (mixed_bounds law c s) x

end SatKUpper.LocalComparison
