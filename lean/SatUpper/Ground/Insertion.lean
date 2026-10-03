import SatUpper.Ground.Finite

/-! Ground-state insertions reduce directly to the ordinary cubic log inequality. -/

open MeasureTheory SatUpper.DirectFinite SatUpper.GroundFinite

namespace SatUpper.GroundInsertion

theorem clause_factor {n K L : ℕ} (y : ℝ) (c : Fin K → Fresh n) (s : Fin L → Fresh n)
    (x : Fresh n) (a : Fields L) :
    Real.exp (-y * energy (Fin.cons x c) s a) =
      Real.exp (-y * energy c s a) * (1-(1-Real.exp (-y))*∏ j, backbone c s (x j) a) := by
  classical
  have he : cost (Fin.cons x c) s a = fun σ =>
      cost c s a σ + if ∀ j, σ (x j).1.1 = (x j).1.2 then 1 else 0 := by
    funext σ
    simp only [cost, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    omega
  have hp : (∀ σ, cost c s a σ = energy c s a → ∀ j, σ (x j).1.1 = (x j).1.2) ↔
      (∀ σ, cost c s a σ = energy c s a → σ (x 0).1.1 = (x 0).1.2) ∧
      (∀ σ, cost c s a σ = energy c s a → σ (x 1).1.1 = (x 1).1.2) ∧
      (∀ σ, cost c s a σ = energy c s a → σ (x 2).1.1 = (x 2).1.2) := by
    simp [Fin.forall_fin_succ, forall_and]
  unfold energy
  rw [he, GroundMinimum.exp_insert]
  change _ = Real.exp (-y * energy c s a) * _
  change Real.exp (-y * energy c s a) * (1-(1-Real.exp (-y))*
    if ∀ σ, cost c s a σ = energy c s a → ∀ j, σ (x j).1.1 = (x j).1.2 then 1 else 0) = _
  simp only [hp, Fin.prod_univ_three, backbone]
  split_ifs <;> simp_all [energy]

theorem site_factor {n K L : ℕ} (y : ℝ) (c : Fin K → Fresh n) (s : Fin L → Fresh n)
    (x : Fresh n) (v : Fin 3 → Bool) (a : Fields L) :
    Real.exp (-y * energy c (Fin.cons x s) (Fin.cons v a)) =
      Real.exp (-y * energy c s a) *
        (1-(1-Real.exp (-y))*backbone c s (x 0) a *
          (if v 1 = true then 1 else 0) * (if v 2 = true then 1 else 0)) := by
  classical
  have he : cost c (Fin.cons x s) (Fin.cons v a) = fun σ =>
      cost c s a σ + if σ (x 0).1.1 = (x 0).1.2 ∧ v 1 = true ∧ v 2 = true then 1 else 0 := by
    funext σ
    simp only [cost, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    omega
  obtain ⟨σ₀,hσ₀⟩ := GroundMinimum.attained (cost c s a)
  change cost c s a σ₀ = energy c s a at hσ₀
  have hp : (∀ σ, cost c s a σ = energy c s a →
      σ (x 0).1.1 = (x 0).1.2 ∧ v 1 = true ∧ v 2 = true) ↔
      (∀ σ, cost c s a σ = energy c s a → σ (x 0).1.1 = (x 0).1.2) ∧
      v 1 = true ∧ v 2 = true := by
    constructor
    · intro h
      exact ⟨fun σ hσ => (h σ hσ).1, (h σ₀ hσ₀).2⟩
    · rintro ⟨h,h₁,h₂⟩ σ hσ
      exact ⟨h σ hσ,h₁,h₂⟩
  unfold energy
  rw [he, GroundMinimum.exp_insert]
  change Real.exp (-y * energy c s a) * (1-(1-Real.exp (-y))*
    if ∀ σ, cost c s a σ = energy c s a →
      σ (x 0).1.1 = (x 0).1.2 ∧ v 1 = true ∧ v 2 = true then 1 else 0) = _
  simp only [hp, backbone]
  split_ifs <;> simp_all [energy]


theorem integral_warning (i : Fin 4) :
    (∫ b : Bool, (if b = true then 1 else 0 : ℝ) ∂TrialFields.stateLaw i) =
      (Formalization.badMass i : ℝ) := by
  have h := integral_indicator_const (1 : ℝ) (measurableSet_singleton true)
    (μ := TrialFields.stateLaw i)
  simpa [Set.indicator, TrialFields.stateLaw_hard] using h

theorem integral_pair {n : ℕ} (x : Fresh n) :
    (∫ v, (if v 1 = true then 1 else 0 : ℝ)*(if v 2 = true then 1 else 0) ∂rowLaw x) =
      (Formalization.badMass (x 1).2 : ℝ)*Formalization.badMass (x 2).2 := by
  have h := integral_fintype_prod_eq_prod
    (μ := fun j : Fin 3 => innerLaw (x j))
    (fun j b => if j = 0 then 1 else if b = true then 1 else 0 : Fin 3 → Bool → ℝ)
  simpa only [Fin.prod_univ_three, if_pos rfl, if_neg (by decide : (1 : Fin 3) ≠ 0),
    if_neg (by decide : (2 : Fin 3) ≠ 0), ite_true, one_mul, integral_const,
    measureReal_univ_eq_one, one_smul, innerLaw, integral_warning, rowLaw] using h

theorem site_moment {n K L : ℕ} (y : ℝ) (c : Fin K → Fresh n) (s : Fin L → Fresh n)
    (x : Fresh n) :
    moment y c (Fin.cons x s) = ∫ a, Real.exp (-y * energy c s a) *
      (1-(1-Real.exp (-y))*∏ j, ReplicaCubic.mixedFamily (backbone c s) rate j (x j) a) ∂fieldLaw s := by
  have he : fieldLaw (Fin.cons x s) = Measure.pi (Fin.cons (rowLaw x) (fun i => rowLaw (s i))) := by
    unfold fieldLaw
    congr 1
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  rw [GroundFinite.moment, he, DirectProduct.integral_cons]
  simp_rw [site_factor]
  apply integral_congr_ae
  filter_upwards [] with a
  simp only [Fin.prod_univ_three, ReplicaCubic.mixedFamily, Fin.val_zero, Fin.val_one,
    Fin.val_two, ite_true, ite_false, Nat.one_ne_zero, OfNat.ofNat_ne_zero, rate]
  simp_rw [mul_assoc]
  rw [integral_const_mul, integral_sub (integrable_const _) Integrable.of_finite,
    integral_const, measureReal_univ_eq_one, one_smul, integral_const_mul, integral_const_mul,
    integral_pair]

theorem log_ratio {n K L : ℕ} (y : ℝ) (c : Fin K → Fresh n) (s : Fin L → Fresh n)
    {Z : Fields L → ℝ} (h0 : ∀ a, 0 ≤ Z a) (h1 : ∀ a, Z a ≤ 1)
    {M : ℝ} (hM : 0 < M)
    (he : M = ∫ a, Real.exp (-y * energy c s a)*(1-(1-Real.exp (-y))*Z a) ∂fieldLaw s) :
    Real.log M - Real.log (moment y c s) =
      Real.log (1-(1-Real.exp (-y))*(∫ a, Z a ∂tilted y c s)) := by
  rw [← Real.log_div hM.ne' (moment_pos y c s).ne', he]
  exact congrArg Real.log (GibbsInsertion.partition_ratio (fieldLaw s) Integrable.of_finite
    (measurable_of_countable _) h0 h1 (1-Real.exp (-y)))


theorem product_bounds {n L : ℕ} (f : Fin 3 → Seed n → Fields L → ℝ)
    (hb : ∀ j x a, 0 ≤ f j x a ∧ f j x a ≤ 1) (x : Fresh n) (a : Fields L) :
    0 ≤ ∏ j, f j (x j) a ∧ (∏ j, f j (x j) a) ≤ 1 :=
  ⟨Finset.prod_nonneg (fun j _ => (hb j (x j) a).1),
    Finset.prod_le_one (fun j _ => (hb j (x j) a).1) (fun j _ => (hb j (x j) a).2)⟩

theorem mixed_bounds {n K L : ℕ} (c : Fin K → Fresh n) (s : Fin L → Fresh n)
    (j : Fin 3) (x : Seed n) (a : Fields L) :
    0 ≤ ReplicaCubic.mixedFamily (backbone c s) rate j x a ∧
      ReplicaCubic.mixedFamily (backbone c s) rate j x a ≤ 1 := by
  unfold ReplicaCubic.mixedFamily
  split
  · exact backbone_bounds c s x a
  · exact rate_bounds x a

theorem clause_increment {n K L : ℕ} (y : ℝ) (c : Fin K → Fresh n) (s : Fin L → Fresh n)
    (x : Fresh n) : entropy y (Fin.cons x c) s - entropy y c s =
      Real.log (1-(1-Real.exp (-y))*LogInsertion.meanProduct (tilted y c s) 3
        (fun _ => backbone c s) x) := by
  have hb := product_bounds (fun _ => backbone c s) (fun _ => backbone_bounds c s) x
  exact log_ratio y c s (fun a => (hb a).1) (fun a => (hb a).2)
    (moment_pos y (Fin.cons x c) s) (by simp_rw [GroundFinite.moment, clause_factor])

theorem site_increment {n K L : ℕ} (y : ℝ) (c : Fin K → Fresh n) (s : Fin L → Fresh n)
    (x : Fresh n) : entropy y c (Fin.cons x s) - entropy y c s =
      Real.log (1-(1-Real.exp (-y))*LogInsertion.meanProduct (tilted y c s) 3
        (ReplicaCubic.mixedFamily (backbone c s) rate) x) := by
  have hb := product_bounds _ (mixed_bounds c s) x
  exact log_ratio y c s (fun a => (hb a).1) (fun a => (hb a).2)
    (moment_pos y c (Fin.cons x s)) (site_moment y c s x)

noncomputable def edgeMean (n : ℕ) [NeZero n] (y : ℝ) : ℝ :=
  ∫ x : Fresh n, Real.log (1-(1-Real.exp (-y))*∏ j, (Formalization.badMass (x j).2 : ℝ)) ∂freshLaw n

theorem cubic_nonpos {n K L : ℕ} [NeZero n] {y : ℝ} (hy : 0 ≤ y)
    (c : Fin K → Fresh n) (s : Fin L → Fresh n) :
    (∫ x, entropy y (Fin.cons x c) s - entropy y c s ∂freshLaw n) -
      3*(∫ x, entropy y c (Fin.cons x s) - entropy y c s ∂freshLaw n) + 2*edgeMean n y ≤ 0 := by
  have h := LogInsertion.cubic_log_insertion_nonpos (seedLaw n) (tilted y c s)
    (b := backbone c s) (c := rate) (measurable_of_countable _) (measurable_of_countable _)
    (fun x a => (backbone_bounds c s x a).1) (fun x a => (backbone_bounds c s x a).2)
    (fun x a => (rate_bounds x a).1) (fun x a => (rate_bounds x a).2)
    (q := 1-Real.exp (-y)) (by linarith [Real.exp_le_one_iff.mpr (neg_nonpos.mpr hy)])
    (by linarith [Real.exp_pos (-y)])
  simp_rw [clause_increment, site_increment]
  simpa only [LogInsertion.insertionLog, LogInsertion.meanProduct, rate, integral_const,
    measureReal_univ_eq_one, one_smul, edgeMean, freshLaw] using h

theorem increment_bound {n K L : ℕ} {y : ℝ} (hy : 0 ≤ y)
    (c : Fin K → Fresh n) (s : Fin L → Fresh n)
    (f : Fin 3 → Seed n → Fields L → ℝ)
    (hb : ∀ j x a, 0 ≤ f j x a ∧ f j x a ≤ 1) (x : Fresh n) :
    ‖Real.log (1-(1-Real.exp (-y))*LogInsertion.meanProduct (tilted y c s) 3 f x)‖ ≤ y := by
  have hz := LogInsertion.meanProduct_bounds (tilted y c s) 3 (fun _ => measurable_of_countable _)
    (fun j x a => (hb j x a).1) (fun j x a => (hb j x a).2) x
  have h := log_factor_bounds hy hz.1 hz.2
  rw [Real.norm_eq_abs, abs_of_nonpos h.2]
  linarith [h.1]

theorem clause_increment_bound {n K L : ℕ} {y : ℝ} (hy : 0 ≤ y)
    (c : Fin K → Fresh n) (s : Fin L → Fresh n) (x : Fresh n) :
    ‖entropy y (Fin.cons x c) s - entropy y c s‖ ≤ y := by
  rw [clause_increment]
  exact increment_bound hy c s _ (fun _ => backbone_bounds c s) x

theorem site_increment_bound {n K L : ℕ} {y : ℝ} (hy : 0 ≤ y)
    (c : Fin K → Fresh n) (s : Fin L → Fresh n) (x : Fresh n) :
    ‖entropy y c (Fin.cons x s) - entropy y c s‖ ≤ y := by
  rw [site_increment]
  exact increment_bound hy c s _ (mixed_bounds c s) x

end SatUpper.GroundInsertion
