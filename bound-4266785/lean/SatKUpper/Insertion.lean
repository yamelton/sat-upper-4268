import SatKUpper.Ground
import SatKUpper.LogInsertion

/-! Exact clause and site insertions for the general finite coin law. -/

open MeasureTheory SatKUpper.Sampling SatKUpper.Ground SatUpper

namespace SatKUpper.Insertion

theorem indicator_forall {ι : Type*} [Fintype ι] (P : ι → Prop) [DecidablePred P]
    [Decidable (∀ i, P i)] :
    (if ∀ i, P i then 1 else 0 : ℝ) = ∏ i, if P i then 1 else 0 := by
  classical
  by_cases h : ∀ i, P i
  · simp [h]
  · rw [if_neg h]
    push_neg at h
    obtain ⟨i, hi⟩ := h
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem clause_factor {t r n K L : ℕ} (y : ℝ) (c : Fin K → Fresh t r n)
    (s : Fin L → Fresh t r n) (x : Fresh t r n) (a : Fields r L) :
    Real.exp (-y * energy (Fin.cons x c) s a) =
      Real.exp (-y * energy c s a) *
        (1-(1-Real.exp (-y))*∏ j, backbone c s (x j) a) := by
  classical
  have he : cost (Fin.cons x c) s a = fun σ =>
      cost c s a σ + if ∀ j, σ (x j).1.1 = (x j).1.2 then 1 else 0 := by
    funext σ
    simp only [cost, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    omega
  have hp : (∀ σ, cost c s a σ = energy c s a → ∀ j, σ (x j).1.1 = (x j).1.2) ↔
      (∀ j, ∀ σ, cost c s a σ = energy c s a → σ (x j).1.1 = (x j).1.2) := by
    constructor
    · intro h j σ hs; exact h σ hs j
    · intro h σ hs j; exact h j σ hs
  unfold energy
  rw [he, GroundMinimum.exp_insert]
  change Real.exp (-y * energy c s a) * (1-(1-Real.exp (-y))*
    if ∀ σ, cost c s a σ = energy c s a → ∀ j, σ (x j).1.1 = (x j).1.2 then 1 else 0) = _
  simp only [hp]
  exact congrArg (fun z : ℝ => Real.exp (-y * energy c s a) * (1-(1-Real.exp (-y))*z))
    (indicator_forall (fun j : Fin (r+1) =>
      ∀ σ, cost c s a σ = energy c s a → σ (x j).1.1 = (x j).1.2))

theorem site_factor {t r n K L : ℕ} (y : ℝ) (c : Fin K → Fresh t r n)
    (s : Fin L → Fresh t r n) (x : Fresh t r n) (v : Fin r → Bool) (a : Fields r L) :
    Real.exp (-y * energy c (Fin.cons x s) (Fin.cons v a)) =
      Real.exp (-y * energy c s a) *
        (1-(1-Real.exp (-y))*(backbone c s (x 0) a *
          ∏ j, if v j = true then 1 else 0)) := by
  classical
  have he : cost c (Fin.cons x s) (Fin.cons v a) = fun σ =>
      cost c s a σ + if σ (x 0).1.1 = (x 0).1.2 ∧ (∀ j, v j = true) then 1 else 0 := by
    funext σ
    simp only [cost, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    omega
  obtain ⟨σ₀,hσ₀⟩ := GroundMinimum.attained (cost c s a)
  change cost c s a σ₀ = energy c s a at hσ₀
  have hp : (∀ σ, cost c s a σ = energy c s a →
      σ (x 0).1.1 = (x 0).1.2 ∧ (∀ j, v j = true)) ↔
      (∀ σ, cost c s a σ = energy c s a → σ (x 0).1.1 = (x 0).1.2) ∧
      (∀ j, v j = true) := by
    constructor
    · intro h
      exact ⟨fun σ hσ => (h σ hσ).1, (h σ₀ hσ₀).2⟩
    · rintro ⟨h,hv⟩ σ hσ
      exact ⟨h σ hσ,hv⟩
  unfold energy
  rw [he, GroundMinimum.exp_insert]
  change Real.exp (-y * energy c s a) * (1-(1-Real.exp (-y))*
    if ∀ σ, cost c s a σ = energy c s a →
      σ (x 0).1.1 = (x 0).1.2 ∧ (∀ j, v j = true) then 1 else 0) = _
  simp only [hp]
  rw [← indicator_forall]
  simp only [backbone]
  split_ifs <;> simp_all [energy]

theorem integral_warning {t : ℕ} (law : CoinLaw t) (i : Fin t) :
    (∫ b : Bool, (if b = true then 1 else 0 : ℝ) ∂stateLaw law i) = law.rate i := by
  have h := integral_indicator_const (1 : ℝ) (measurableSet_singleton true)
    (μ := stateLaw law i)
  simpa [Set.indicator, stateLaw_true] using h

theorem integral_warnings {t r n : ℕ} (law : CoinLaw t) (x : Fresh t r n) :
    (∫ v, (∏ j, if v j = true then 1 else 0 : ℝ) ∂rowLaw law x) =
      ∏ j : Fin r, law.rate (x j.succ).2 := by
  have h := integral_fintype_prod_eq_prod
    (μ := fun j : Fin r => stateLaw law (x j.succ).2)
    (fun _ b => if b = true then 1 else 0 : Fin r → Bool → ℝ)
  simpa only [integral_warning, rowLaw] using h

theorem mixed_product {t r n K L : ℕ} (law : CoinLaw t) (c : Fin K → Fresh t r n)
    (s : Fin L → Fresh t r n) (x : Fresh t r n) (a : Fields r L) :
    (∏ j, ReplicaPower.mixedFamily r (backbone c s) (rate law) j (x j) a) =
      backbone c s (x 0) a * ∏ j : Fin r, law.rate (x j.succ).2 := by
  simp [Fin.prod_univ_succ, ReplicaPower.mixedFamily, rate]

theorem site_moment {t r n K L : ℕ} (law : CoinLaw t) (y : ℝ)
    (c : Fin K → Fresh t r n) (s : Fin L → Fresh t r n) (x : Fresh t r n) :
    moment law y c (Fin.cons x s) = ∫ a, Real.exp (-y * energy c s a) *
      (1-(1-Real.exp (-y))*∏ j,
        ReplicaPower.mixedFamily r (backbone c s) (rate law) j (x j) a) ∂fieldLaw law s := by
  have he : fieldLaw law (Fin.cons x s) =
      Measure.pi (Fin.cons (rowLaw law x) (fun i => rowLaw law (s i))) := by
    unfold fieldLaw
    congr 1
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  rw [moment, he, DirectProduct.integral_cons]
  simp_rw [site_factor, mixed_product]
  apply integral_congr_ae
  filter_upwards [] with a
  rw [integral_const_mul, integral_sub (integrable_const _) Integrable.of_finite,
    integral_const, measureReal_univ_eq_one, one_smul, integral_const_mul,
    integral_const_mul, integral_warnings]

theorem log_ratio {t r n K L : ℕ} (law : CoinLaw t) (y : ℝ)
    (c : Fin K → Fresh t r n) (s : Fin L → Fresh t r n)
    {Z : Fields r L → ℝ} (h0 : ∀ a, 0 ≤ Z a) (h1 : ∀ a, Z a ≤ 1)
    {M : ℝ} (hM : 0 < M)
    (he : M = ∫ a, Real.exp (-y * energy c s a)*(1-(1-Real.exp (-y))*Z a) ∂fieldLaw law s) :
    Real.log M - Real.log (moment law y c s) =
      Real.log (1-(1-Real.exp (-y))*(∫ a, Z a ∂tilted law y c s)) := by
  rw [← Real.log_div hM.ne' (moment_pos law y c s).ne', he]
  exact congrArg Real.log (GibbsInsertion.partition_ratio (fieldLaw law s) Integrable.of_finite
    (measurable_of_countable _) h0 h1 (1-Real.exp (-y)))

end SatKUpper.Insertion
