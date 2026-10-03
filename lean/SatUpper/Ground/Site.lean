import SatUpper.Ground.Comparison
import SatUpper.SiteSideLaw

/-! A conflicting pair of warning sides costs at least one violation.
Independent vertex sides then give the site endpoint bound. -/

open MeasureTheory SatUpper.DirectFinite SatUpper.GroundFinite SatUpper.SiteVertexIdentity

namespace SatUpper.GroundSite

abbrev Locations (n L : ℕ) := Fin L → Fin 3 → Fin n × Bool
abbrev Surveys (L : ℕ) := (Fin L × Fin 3) → Fin 4

def pack {n L : ℕ} (u : Locations n L) (q : Surveys L) : Fin L → Fresh n :=
  fun i j => (u i j,q (i,j))

noncomputable def conflict {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : (ι → TrialFields.InnerMark) × (κ → TrialFields.InnerMark)) : ℕ := by
  classical
  exact if x ∈ TrialVertex.goodEvent ι κ then 0 else 1

noncomputable def localCost {n L : ℕ} (u : Locations n L) (x : (Fin L × Fin 3) → Bool)
    (v : Fin n) (b : Bool) : ℕ :=
  ∑ i, if (u i 0).1 = v then
    if b = (u i 0).2 ∧ x (i,1) = true ∧ x (i,2) = true then 1 else 0 else 0

theorem cost_eq_sum {n L : ℕ} (u : Locations n L) (q : Surveys L)
    (x : (Fin L × Fin 3) → Bool) (σ : Spin n) :
    cost Fin.elim0 (pack u q) (Function.curry x) σ = ∑ v, localCost u x v (σ v) := by
  classical
  unfold localCost
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp [cost, pack, Function.curry]

theorem conflict_le {n L : ℕ} (u : Locations n L) (x : (Fin L × Fin 3) → Bool)
    (v : Fin n) (b : Bool) :
    conflict (messages u v true x, messages u v false x) ≤ localCost u x v b := by
  classical
  unfold conflict
  split
  · exact Nat.zero_le _
  · rename_i h
    obtain ⟨ht,hf⟩ := TrialVertex.bad_event_warnings h
    have hw : ∃ i : Side u v b, messages u v b x i = (true,true) := by
      cases b <;> assumption
    obtain ⟨i,hi⟩ := hw
    have hs := Finset.single_le_sum (f := fun i : Fin L =>
      if (u i 0).1 = v then if b = (u i 0).2 ∧ x (i,1) = true ∧ x (i,2) = true
        then 1 else 0 else 0) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i.val)
    have h₁ : x (i.val,1) = true := congrArg Prod.fst hi
    have h₂ : x (i.val,2) = true := congrArg Prod.snd hi
    simpa [localCost, i.property.1, i.property.2, h₁, h₂] using hs

theorem conflicts_le_energy {n L : ℕ} (u : Locations n L) (q : Surveys L)
    (x : (Fin L × Fin 3) → Bool) :
    (∑ v, conflict (messages u v true x, messages u v false x)) ≤
      energy Fin.elim0 (pack u q) (Function.curry x) := by
  apply GroundMinimum.le_value
  intro σ
  rw [cost_eq_sum]
  exact Finset.sum_le_sum (fun v _ => conflict_le u x v (σ v))

theorem vertex_moment {ι κ : Type*} [Fintype ι] [Fintype κ]
    (y : ℝ) (a : ι → WitnessVertex.Mark) (b : κ → WitnessVertex.Mark) :
    (∫ x, Real.exp (-y * conflict x) ∂TrialVertex.innerLaw a b) =
      noConflict (∏ i, WitnessVertex.mark (a i)) (∏ i, WitnessVertex.mark (b i)) +
      (1-noConflict (∏ i, WitnessVertex.mark (a i)) (∏ i, WitnessVertex.mark (b i)))*Real.exp (-y) := by
  classical
  have he (x : (ι → TrialFields.InnerMark) × (κ → TrialFields.InnerMark)) :
      Real.exp (-y * conflict x) = Real.exp (-y) +
        (1-Real.exp (-y)) * (TrialVertex.goodEvent ι κ).indicator (fun _ => (1 : ℝ)) x := by
    by_cases h : x ∈ TrialVertex.goodEvent ι κ <;> simp [conflict, h]
  simp_rw [he]
  rw [integral_add (integrable_const _) Integrable.of_finite, integral_const_mul,
    integral_indicator_const _ (TrialVertex.measurable_goodEvent ι κ),
    integral_const, measureReal_univ_eq_one, one_smul, smul_eq_mul, mul_one,
    TrialVertex.good_event_probability]
  ring

theorem entropy_le {n L : ℕ} {y : ℝ} (hy : 0 ≤ y) (u : Locations n L) (q : Surveys L) :
    entropy y Fin.elim0 (pack u q) ≤ ∑ v : Fin n,
      Real.log (∫ x, Real.exp (-y * conflict x) ∂TrialVertex.innerLaw
        (SiteSideLaw.surveys u v true q) (SiteSideLaw.surveys u v false q)) := by
  have hb (x : (Fin L × Fin 3) → Bool) :
      Real.exp (-y * energy Fin.elim0 (pack u q) (Function.curry x)) ≤
      ∏ v, Real.exp (-y * conflict (messages u v true x, messages u v false x)) := by
    rw [← Real.exp_sum]
    simp only [← Finset.mul_sum, ← Nat.cast_sum]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left
      (by exact_mod_cast conflicts_le_energy u q x) (neg_nonpos.mpr hy))
  have he : moment y Fin.elim0 (pack u q) = ∫ x,
      Real.exp (-y * energy Fin.elim0 (pack u q) (Function.curry x))
        ∂Measure.pi (fun p => TrialFields.stateLaw (q p)) := by
    rw [← ProductMeasures.uncurry (fun i j => TrialFields.stateLaw (q (i,j))),
      integral_map (measurable_of_countable _).aemeasurable (measurable_of_countable _).aestronglyMeasurable]
    rfl
  have h := integral_mono (μ := Measure.pi (fun p => TrialFields.stateLaw (q p)))
    Integrable.of_finite Integrable.of_finite hb
  rw [← he] at h
  have hf : (∫ x : (Fin L × Fin 3) → Bool,
      ∏ v, Real.exp (-y * conflict (messages u v true x, messages u v false x))
        ∂Measure.pi (fun p => TrialFields.stateLaw (q p))) =
      ∏ v, ∫ x, Real.exp (-y * conflict x) ∂TrialVertex.innerLaw
        (SiteSideLaw.surveys u v true q) (SiteSideLaw.surveys u v false q) := by
    rw [← integral_fintype_prod_eq_prod, ← SiteSideLaw.joint_law u q,
      integral_map (measurable_of_countable _).aemeasurable (measurable_of_countable _).aestronglyMeasurable]
  rw [hf] at h
  have hl := Real.log_le_log (moment_pos y Fin.elim0 (pack u q)) h
  rwa [Real.log_prod _ _ (fun v _ => (integral_exp_pos (μ := TrialVertex.innerLaw
    (SiteSideLaw.surveys u v true q) (SiteSideLaw.surveys u v false q)) Integrable.of_finite).ne')] at hl

end SatUpper.GroundSite
