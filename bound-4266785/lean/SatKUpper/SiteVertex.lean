import SatKUpper.Insertion
import SatUpper.TrialVertex

/-! Warning and conflict probabilities for any number of replacement coins. -/

open MeasureTheory SatKUpper.Sampling SatUpper

namespace SatKUpper.SiteVertex

abbrev Mark (t r : ℕ) := Fin r → Fin t
abbrev Message (r : ℕ) := Fin r → Bool

noncomputable def mark {t r : ℕ} (law : CoinLaw t) (a : Mark t r) : ℝ :=
  1 - ∏ j, law.rate (a j)

theorem mark_bounds {t r : ℕ} (law : CoinLaw t) (a : Mark t r) :
    0 ≤ mark law a ∧ mark law a ≤ 1 := by
  have h0 := Finset.prod_nonneg (s := Finset.univ) (fun j _ => law.nonneg (a j))
  have h1 := Finset.prod_le_one (s := Finset.univ)
    (fun j _ => law.nonneg (a j)) (fun j _ => (law.lt_one (a j)).le)
  constructor <;> unfold mark <;> linarith

noncomputable def messageLaw {t r : ℕ} (law : CoinLaw t) (a : Mark t r) :
    Measure (Message r) := Measure.pi (fun j => stateLaw law (a j))

instance {t r : ℕ} (law : CoinLaw t) (a : Mark t r) :
    IsProbabilityMeasure (messageLaw law a) := by unfold messageLaw; infer_instance

theorem messageLaw_warning {t r : ℕ} (law : CoinLaw t) (a : Mark t r) :
    (messageLaw law a).real {fun _ => true} = ∏ j, law.rate (a j) := by
  have he : ({fun _ : Fin r => true} : Set (Message r)) =
      Set.univ.pi (fun _ => {true}) := by ext x; simp [Set.mem_pi, funext_iff]
  rw [he, measureReal_def, messageLaw, Measure.pi_pi, ENNReal.toReal_prod]
  exact Finset.prod_congr rfl (fun j _ => stateLaw_true law (a j))

theorem messageLaw_noWarning {t r : ℕ} (law : CoinLaw t) (a : Mark t r) :
    (messageLaw law a).real ({fun _ => true}ᶜ) = mark law a := by
  rw [measureReal_compl (measurableSet_singleton _), messageLaw_warning]
  simp [mark]

variable {t r : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

noncomputable def sideLaw (law : CoinLaw t) (a : ι → Mark t r) :
    Measure (ι → Message r) := Measure.pi (fun i => messageLaw law (a i))

instance (law : CoinLaw t) (a : ι → Mark t r) : IsProbabilityMeasure (sideLaw law a) := by
  unfold sideLaw; infer_instance

def noWarning (r : ℕ) (ι : Type*) : Set (ι → Message r) :=
  Set.univ.pi (fun _ => {fun _ => true}ᶜ)

theorem measurable_noWarning (r : ℕ) (ι : Type*) [Fintype ι] :
    MeasurableSet (noWarning r ι) := (Set.to_countable _).measurableSet

theorem noWarning_probability (law : CoinLaw t) (a : ι → Mark t r) :
    (sideLaw law a).real (noWarning r ι) = ∏ i, mark law (a i) := by
  rw [measureReal_def, sideLaw, noWarning, Measure.pi_pi, ENNReal.toReal_prod]
  exact Finset.prod_congr rfl (fun i _ => messageLaw_noWarning law (a i))

noncomputable def innerLaw (law : CoinLaw t) (a : ι → Mark t r) (b : κ → Mark t r) :
    Measure ((ι → Message r) × (κ → Message r)) :=
  (sideLaw law a).prod (sideLaw law b)

instance (law : CoinLaw t) (a : ι → Mark t r) (b : κ → Mark t r) :
    IsProbabilityMeasure (innerLaw law a b) := by unfold innerLaw; infer_instance

def goodEvent (r : ℕ) (ι κ : Type*) : Set ((ι → Message r) × (κ → Message r)) :=
  ((noWarning r ι)ᶜ ×ˢ (noWarning r κ)ᶜ)ᶜ

theorem measurable_goodEvent (r : ℕ) (ι κ : Type*) [Fintype ι] [Fintype κ] :
    MeasurableSet (goodEvent r ι κ) :=
  ((measurable_noWarning r ι).compl.prod (measurable_noWarning r κ).compl).compl

theorem bad_event_probability (law : CoinLaw t) (a : ι → Mark t r) (b : κ → Mark t r) :
    (innerLaw law a b).real ((noWarning r ι)ᶜ ×ˢ (noWarning r κ)ᶜ) =
      (1-∏ i, mark law (a i))*(1-∏ i, mark law (b i)) := by
  rw [measureReal_def, innerLaw, Measure.prod_prod, ENNReal.toReal_mul]
  change (sideLaw law a).real ((noWarning r ι)ᶜ) *
    (sideLaw law b).real ((noWarning r κ)ᶜ) = _
  rw [measureReal_compl (measurable_noWarning r ι),
    measureReal_compl (measurable_noWarning r κ), noWarning_probability, noWarning_probability]
  simp

theorem good_event_probability (law : CoinLaw t) (a : ι → Mark t r) (b : κ → Mark t r) :
    (innerLaw law a b).real (goodEvent r ι κ) =
      noConflict (∏ i, mark law (a i)) (∏ i, mark law (b i)) := by
  rw [goodEvent, measureReal_compl
    ((measurable_noWarning r ι).compl.prod (measurable_noWarning r κ).compl),
    bad_event_probability, noConflict_complement]
  simp

omit [Fintype ι] [Fintype κ] in
theorem bad_event_warnings {x : (ι → Message r) × (κ → Message r)}
    (hx : x ∉ goodEvent r ι κ) :
    (∃ i, x.1 i = fun _ => true) ∧ (∃ j, x.2 j = fun _ => true) := by
  classical
  simpa [goodEvent, noWarning, Set.mem_pi] using hx

noncomputable def conflict (x : (ι → Message r) × (κ → Message r)) : ℕ := by
  classical
  exact if x ∈ goodEvent r ι κ then 0 else 1

theorem vertex_moment (law : CoinLaw t) (y : ℝ)
    (a : ι → Mark t r) (b : κ → Mark t r) :
    (∫ x, Real.exp (-y * conflict x) ∂innerLaw law a b) =
      noConflict (∏ i, mark law (a i)) (∏ i, mark law (b i)) +
      (1-noConflict (∏ i, mark law (a i)) (∏ i, mark law (b i)))*Real.exp (-y) := by
  classical
  have he (x : (ι → Message r) × (κ → Message r)) :
      Real.exp (-y * conflict x) = Real.exp (-y) +
        (1-Real.exp (-y)) * (goodEvent r ι κ).indicator (fun _ => (1 : ℝ)) x := by
    by_cases h : x ∈ goodEvent r ι κ <;> simp [conflict, h]
  simp_rw [he]
  rw [integral_add (integrable_const _) Integrable.of_finite, integral_const_mul,
    integral_indicator_const _ (measurable_goodEvent r ι κ),
    integral_const, measureReal_univ_eq_one, one_smul, smul_eq_mul, mul_one,
    good_event_probability]
  ring

end SatKUpper.SiteVertex
