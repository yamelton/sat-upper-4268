import SatUpper.TrialFields
import Mathlib.MeasureTheory.Constructions.Pi

/-! Conditional no-warning and no-conflict events under the actual finite trial laws. -/

open MeasureTheory
open SatUpper.TrialFields SatUpper.WitnessVertex

namespace SatUpper.TrialVertex

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem messageLaw_noWarning (a : Mark) :
    (messageLaw a).real ({(true,true)}ᶜ) = mark a := by
  rw [measureReal_compl (measurableSet_singleton _), messageLaw_hard]
  simp [mark]

noncomputable def sideLaw (a : ι → Mark) : Measure (ι → InnerMark) :=
  Measure.pi (fun i => messageLaw (a i))

instance (a : ι → Mark) : IsProbabilityMeasure (sideLaw a) := by
  unfold sideLaw
  infer_instance

def noWarning (ι : Type*) : Set (ι → InnerMark) :=
  Set.univ.pi (fun _ => {(true,true)}ᶜ)

theorem measurable_noWarning (ι : Type*) [Fintype ι] : MeasurableSet (noWarning ι) :=
  (Set.to_countable _).measurableSet

theorem noWarning_probability (a : ι → Mark) :
    (sideLaw a).real (noWarning ι) = ∏ i, mark (a i) := by
  rw [measureReal_def, sideLaw, noWarning, Measure.pi_pi, ENNReal.toReal_prod]
  exact Finset.prod_congr rfl (fun i _ => messageLaw_noWarning (a i))

noncomputable def innerLaw (a : ι → Mark) (b : κ → Mark) :
    Measure ((ι → InnerMark) × (κ → InnerMark)) :=
  (sideLaw a).prod (sideLaw b)

instance (a : ι → Mark) (b : κ → Mark) :
    IsProbabilityMeasure (innerLaw a b) := by
  unfold innerLaw
  infer_instance

def goodEvent (ι κ : Type*) : Set ((ι → InnerMark) × (κ → InnerMark)) :=
  ((noWarning ι)ᶜ ×ˢ (noWarning κ)ᶜ)ᶜ

theorem measurable_goodEvent (ι κ : Type*) [Fintype ι] [Fintype κ] : MeasurableSet (goodEvent ι κ) :=
  ((measurable_noWarning ι).compl.prod (measurable_noWarning κ).compl).compl

theorem bad_event_probability (a : ι → Mark) (b : κ → Mark) :
    (innerLaw a b).real ((noWarning ι)ᶜ ×ˢ (noWarning κ)ᶜ) =
      (1-∏ i, mark (a i))*(1-∏ i, mark (b i)) := by
  rw [measureReal_def, innerLaw, Measure.prod_prod, ENNReal.toReal_mul]
  change (sideLaw a).real ((noWarning ι)ᶜ) * (sideLaw b).real ((noWarning κ)ᶜ) = _
  rw [measureReal_compl (measurable_noWarning ι), measureReal_compl (measurable_noWarning κ),
    noWarning_probability, noWarning_probability]
  simp

theorem good_event_probability (a : ι → Mark) (b : κ → Mark) :
    (innerLaw a b).real (goodEvent ι κ) = noConflict (∏ i, mark (a i)) (∏ i, mark (b i)) := by
  rw [goodEvent, measureReal_compl
    ((measurable_noWarning ι).compl.prod (measurable_noWarning κ).compl),
    bad_event_probability, noConflict_complement]
  simp

omit [Fintype ι] [Fintype κ] in
theorem bad_event_warnings {x : (ι → InnerMark) × (κ → InnerMark)}
    (hx : x ∉ goodEvent ι κ) : (∃ i, x.1 i = (true,true)) ∧ (∃ j, x.2 j = (true,true)) := by
  classical
  simpa [goodEvent, noWarning, Set.mem_pi] using hx

end SatUpper.TrialVertex
