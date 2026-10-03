import SatUpper.Direct.Product
import SatUpper.Ground.Minimum
import SatUpper.GibbsInsertion
import SatUpper.LogInsertion

/-! Conditional exponential moments of the integer minimum violation count. -/

open MeasureTheory SatUpper.DirectFinite

namespace SatUpper.GroundFinite

noncomputable def cost {n K L : ℕ} (c : Fin K → Fresh n) (s : Fin L → Fresh n)
    (a : Fields L) (σ : Spin n) : ℕ :=
  (∑ i, if ∀ j, σ (c i j).1.1 = (c i j).1.2 then 1 else 0) +
    ∑ i, if σ (s i 0).1.1 = (s i 0).1.2 ∧ a i 1 = true ∧ a i 2 = true then 1 else 0

noncomputable def energy {n K L : ℕ} (c : Fin K → Fresh n) (s : Fin L → Fresh n)
    (a : Fields L) : ℕ := GroundMinimum.value (cost c s a)

noncomputable def moment {n K L : ℕ} (y : ℝ) (c : Fin K → Fresh n) (s : Fin L → Fresh n) : ℝ :=
  ∫ a, Real.exp (-y * energy c s a) ∂fieldLaw s

noncomputable def entropy {n K L : ℕ} (y : ℝ) (c : Fin K → Fresh n) (s : Fin L → Fresh n) : ℝ :=
  Real.log (moment y c s)

theorem moment_pos {n K L : ℕ} (y : ℝ) (c : Fin K → Fresh n) (s : Fin L → Fresh n) :
    0 < moment y c s := integral_exp_pos Integrable.of_finite

theorem energy_le {n K L : ℕ} (c : Fin K → Fresh n) (s : Fin L → Fresh n) (a : Fields L) :
    energy c s a ≤ K + L := by
  refine (GroundMinimum.value_le _ (fun _ => false)).trans ?_
  have h (P : Prop) [Decidable P] : (if P then 1 else 0 : ℕ) ≤ 1 := by split <;> omega
  have h₁ := Finset.sum_le_sum (s := Finset.univ) (fun i _ => h (∀ j, (fun _ => false) (c i j).1.1 = (c i j).1.2))
  have h₂ := Finset.sum_le_sum (s := Finset.univ) (fun i _ => h ((fun _ => false) (s i 0).1.1 = (s i 0).1.2 ∧ a i 1 = true ∧ a i 2 = true))
  simpa [cost] using Nat.add_le_add h₁ h₂

theorem entropy_bounds {n K L : ℕ} {y : ℝ} (hy : 0 ≤ y)
    (c : Fin K → Fresh n) (s : Fin L → Fresh n) :
    -y*(K+L) ≤ entropy y c s ∧ entropy y c s ≤ 0 := by
  have hl : Real.exp (-y*(K+L)) ≤ moment y c s := by
    have hb (a : Fields L) : (energy c s a : ℝ) ≤ K+L := by
      exact_mod_cast energy_le c s a
    simpa [moment] using integral_mono (μ := fieldLaw s) (integrable_const (Real.exp (-y*(K+L))))
      Integrable.of_finite (fun a => Real.exp_le_exp.mpr
        (mul_le_mul_of_nonpos_left (hb a) (neg_nonpos.mpr hy)))
  have hu : moment y c s ≤ 1 := by
    simpa [moment] using integral_mono (μ := fieldLaw s) Integrable.of_finite (integrable_const (1 : ℝ))
      (fun a => Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr hy) (Nat.cast_nonneg (energy c s a))))
  exact ⟨by simpa [entropy] using Real.log_le_log (Real.exp_pos _) hl,
    Real.log_nonpos (moment_pos y c s).le hu⟩

noncomputable def tilted {n K L : ℕ} (y : ℝ) (c : Fin K → Fresh n) (s : Fin L → Fresh n) :
    Measure (Fields L) := (fieldLaw s).tilted (fun a => -y * energy c s a)

instance {n K L : ℕ} (y : ℝ) (c : Fin K → Fresh n) (s : Fin L → Fresh n) :
    IsProbabilityMeasure (tilted y c s) := isProbabilityMeasure_tilted Integrable.of_finite

noncomputable def backbone {n K L : ℕ} (c : Fin K → Fresh n) (s : Fin L → Fresh n)
    (x : Seed n) (a : Fields L) : ℝ :=
  if ∀ σ, cost c s a σ = energy c s a → σ x.1.1 = x.1.2 then 1 else 0

noncomputable def rate {n L : ℕ} (x : Seed n) (_ : Fields L) : ℝ := Formalization.badMass x.2

theorem backbone_bounds {n K L : ℕ} (c : Fin K → Fresh n) (s : Fin L → Fresh n)
    (x : Seed n) (a : Fields L) : 0 ≤ backbone c s x a ∧ backbone c s x a ≤ 1 := by
  unfold backbone
  split <;> norm_num

theorem rate_bounds {n L : ℕ} (x : Seed n) (a : Fields L) : 0 ≤ rate x a ∧ rate x a ≤ 1 :=
  ⟨(TrialFields.badMass_bounds x.2).1, (TrialFields.badMass_bounds x.2).2.le⟩

theorem log_factor_bounds {y z : ℝ} (hy : 0 ≤ y) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    -y ≤ Real.log (1-(1-Real.exp (-y))*z) ∧ Real.log (1-(1-Real.exp (-y))*z) ≤ 0 := by
  have hb := factor_bounds (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hy)) hz0 hz1
  exact ⟨by simpa using Real.log_le_log (Real.exp_pos _) hb.1,
    Real.log_nonpos ((Real.exp_pos _).le.trans hb.1) hb.2⟩

/-- A finite nested partition moment, corresponding in form to Franz–Leone
(45), https://arxiv.org/pdf/cond-mat/0208280. The integrand equals `Z_β^m`.
This definition uses our fixed field law; it does not identify that law with
their reweighted measure (46). -/
noncomputable def fractionalEntropy {n K L : ℕ} (m β : ℝ)
    (c : Fin K → Fresh n) (s : Fin L → Fresh n) : ℝ :=
  Real.log (∫ a, Real.exp (m * Real.log (∑ σ : Spin n, Real.exp (-β * cost c s a σ))) ∂fieldLaw s)

/-- A quantitative bridge to the fractional-moment formulation: its normalized
error is at most `m log 2`. Thus `mβ=y` gives the finite-system energetic limit
as `m→0`. No limit interchange is used in the SAT proof. -/
theorem fractional_entropy_bounds {n K L : ℕ} {m β : ℝ} (hm : 0 ≤ m) (hβ : 0 ≤ β)
    (c : Fin K → Fresh n) (s : Fin L → Fresh n) :
    entropy (m*β) c s ≤ fractionalEntropy m β c s ∧
      fractionalEntropy m β c s ≤ entropy (m*β) c s + m*n*Real.log 2 := by
  have hb (a : Fields L) := GroundMinimum.log_partition_bounds (cost c s a) hβ
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow,
    Nat.cast_ofNat, Real.log_pow] at hb
  have hlo (a : Fields L) : Real.exp (-(m*β)*energy c s a) ≤
      Real.exp (m * Real.log (∑ σ : Spin n, Real.exp (-β * cost c s a σ))) := by
    apply Real.exp_le_exp.mpr
    unfold energy
    nlinarith [mul_le_mul_of_nonneg_left (hb a).1 hm]
  have hup (a : Fields L) :
      Real.exp (m * Real.log (∑ σ : Spin n, Real.exp (-β * cost c s a σ))) ≤
        Real.exp (m*n*Real.log 2) * Real.exp (-(m*β)*energy c s a) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    unfold energy
    nlinarith [mul_le_mul_of_nonneg_left (hb a).2 hm]
  have hl := integral_mono (μ := fieldLaw s) Integrable.of_finite Integrable.of_finite hlo
  have hu := integral_mono (μ := fieldLaw s) Integrable.of_finite Integrable.of_finite hup
  rw [integral_const_mul] at hu
  refine ⟨Real.log_le_log (moment_pos (m*β) c s) hl, ?_⟩
  have h := Real.log_le_log ((moment_pos (m*β) c s).trans_le hl) hu
  change fractionalEntropy m β c s ≤ Real.log (Real.exp (m*n*Real.log 2) * moment (m*β) c s) at h
  rw [Real.log_mul (Real.exp_ne_zero _) (moment_pos (m*β) c s).ne', Real.log_exp] at h
  simpa only [entropy, add_comm] using h

end SatUpper.GroundFinite
