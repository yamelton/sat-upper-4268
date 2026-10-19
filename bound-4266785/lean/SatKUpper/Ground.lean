import SatKUpper.Sampling
import SatUpper.Ground.Minimum
import SatUpper.GibbsInsertion
import SatUpper.Ground.Finite

/-! Integer minimum costs for clauses of size r+1 and r replacement coins. -/

open MeasureTheory SatKUpper.Sampling SatUpper

namespace SatKUpper.Ground

noncomputable def cost {t r n K L : ℕ} (c : Fin K → Fresh t r n)
    (s : Fin L → Fresh t r n) (a : Fields r L) (σ : Spin n) : ℕ :=
  (∑ i, if ∀ j, σ (c i j).1.1 = (c i j).1.2 then 1 else 0) +
    ∑ i, if σ (s i 0).1.1 = (s i 0).1.2 ∧ (∀ j, a i j = true) then 1 else 0

noncomputable def energy {t r n K L : ℕ} (c : Fin K → Fresh t r n)
    (s : Fin L → Fresh t r n) (a : Fields r L) : ℕ := GroundMinimum.value (cost c s a)

noncomputable def moment {t r n K L : ℕ} (law : CoinLaw t) (y : ℝ)
    (c : Fin K → Fresh t r n) (s : Fin L → Fresh t r n) : ℝ :=
  ∫ a, Real.exp (-y * energy c s a) ∂fieldLaw law s

noncomputable def entropy {t r n K L : ℕ} (law : CoinLaw t) (y : ℝ)
    (c : Fin K → Fresh t r n) (s : Fin L → Fresh t r n) : ℝ :=
  Real.log (moment law y c s)

theorem moment_pos {t r n K L : ℕ} (law : CoinLaw t) (y : ℝ)
    (c : Fin K → Fresh t r n) (s : Fin L → Fresh t r n) :
    0 < moment law y c s := integral_exp_pos Integrable.of_finite

theorem energy_le {t r n K L : ℕ} (c : Fin K → Fresh t r n)
    (s : Fin L → Fresh t r n) (a : Fields r L) : energy c s a ≤ K+L := by
  refine (GroundMinimum.value_le _ (fun _ => false)).trans ?_
  have h (P : Prop) [Decidable P] : (if P then 1 else 0 : ℕ) ≤ 1 := by split <;> omega
  have h₁ := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => h (∀ j, (fun _ => false) (c i j).1.1 = (c i j).1.2))
  have h₂ := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => h ((fun _ => false) (s i 0).1.1 = (s i 0).1.2 ∧ (∀ j, a i j = true)))
  simpa [cost] using Nat.add_le_add h₁ h₂

theorem entropy_bounds {t r n K L : ℕ} (law : CoinLaw t) {y : ℝ} (hy : 0 ≤ y)
    (c : Fin K → Fresh t r n) (s : Fin L → Fresh t r n) :
    -y*(K+L) ≤ entropy law y c s ∧ entropy law y c s ≤ 0 := by
  have hl : Real.exp (-y*(K+L)) ≤ moment law y c s := by
    have hb (a : Fields r L) : (energy c s a : ℝ) ≤ K+L := by
      exact_mod_cast energy_le c s a
    simpa [moment] using integral_mono (μ := fieldLaw law s)
      (integrable_const (Real.exp (-y*(K+L)))) Integrable.of_finite
      (fun a => Real.exp_le_exp.mpr
        (mul_le_mul_of_nonpos_left (hb a) (neg_nonpos.mpr hy)))
  have hu : moment law y c s ≤ 1 := by
    simpa [moment] using integral_mono (μ := fieldLaw law s)
      Integrable.of_finite (integrable_const (1 : ℝ))
      (fun a => Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr hy) (Nat.cast_nonneg (energy c s a))))
  exact ⟨by simpa [entropy] using Real.log_le_log (Real.exp_pos _) hl,
    Real.log_nonpos (moment_pos law y c s).le hu⟩

noncomputable def tilted {t r n K L : ℕ} (law : CoinLaw t) (y : ℝ)
    (c : Fin K → Fresh t r n) (s : Fin L → Fresh t r n) : Measure (Fields r L) :=
  (fieldLaw law s).tilted (fun a => -y * energy c s a)

instance {t r n K L : ℕ} (law : CoinLaw t) (y : ℝ)
    (c : Fin K → Fresh t r n) (s : Fin L → Fresh t r n) :
    IsProbabilityMeasure (tilted law y c s) := isProbabilityMeasure_tilted Integrable.of_finite

noncomputable def backbone {t r n K L : ℕ} (c : Fin K → Fresh t r n)
    (s : Fin L → Fresh t r n) (x : Seed t n) (a : Fields r L) : ℝ :=
  if ∀ σ, cost c s a σ = energy c s a → σ x.1.1 = x.1.2 then 1 else 0

noncomputable def rate {t r n L : ℕ} (law : CoinLaw t) (x : Seed t n)
    (_ : Fields r L) : ℝ := law.rate x.2

theorem backbone_bounds {t r n K L : ℕ} (c : Fin K → Fresh t r n)
    (s : Fin L → Fresh t r n) (x : Seed t n) (a : Fields r L) :
    0 ≤ backbone c s x a ∧ backbone c s x a ≤ 1 := by
  unfold backbone
  split <;> norm_num

theorem rate_bounds {t r n L : ℕ} (law : CoinLaw t) (x : Seed t n) (a : Fields r L) :
    0 ≤ rate law x a ∧ rate law x a ≤ 1 := ⟨law.nonneg x.2, (law.lt_one x.2).le⟩

end SatKUpper.Ground
