import SatUpper.Direct.Product

/-! Finite coin distributions and clause/site sampling for arbitrary arity.
The type parameter r counts replaced literals: the clause size is r+1.
Unlike the original numerical instance, neither the rates nor their weights
are fixed here. -/

open MeasureTheory

namespace SatKUpper.Sampling

structure CoinLaw (t : ℕ) where
  measure : Measure (Fin t)
  probability : IsProbabilityMeasure measure
  rate : Fin t → ℝ
  nonneg : ∀ i, 0 ≤ rate i
  lt_one : ∀ i, rate i < 1

attribute [instance] CoinLaw.probability

abbrev Spin (n : ℕ) := Fin n → Bool
abbrev Seed (t n : ℕ) := (Fin n × Bool) × Fin t
abbrev Fresh (t r n : ℕ) := Fin (r+1) → Seed t n
abbrev Fields (r L : ℕ) := Fin L → Fin r → Bool

noncomputable def seedLaw {t : ℕ} (law : CoinLaw t) (n : ℕ) [NeZero n] :
    Measure (Seed t n) := (SatUpper.DirectFinite.uniform (Fin n × Bool)).prod law.measure

instance {t : ℕ} (law : CoinLaw t) (n : ℕ) [NeZero n] :
    IsProbabilityMeasure (seedLaw law n) := by unfold seedLaw; infer_instance

noncomputable def freshLaw {t : ℕ} (law : CoinLaw t) (r n : ℕ) [NeZero n] :
    Measure (Fresh t r n) := Measure.pi (fun _ => seedLaw law n)

instance {t : ℕ} (law : CoinLaw t) (r n : ℕ) [NeZero n] :
    IsProbabilityMeasure (freshLaw law r n) := by unfold freshLaw; infer_instance

noncomputable def stateLaw {t : ℕ} (law : CoinLaw t) (i : Fin t) : Measure Bool :=
  (PMF.bernoulli ⟨law.rate i, law.nonneg i⟩ (law.lt_one i).le).toMeasure

instance {t : ℕ} (law : CoinLaw t) (i : Fin t) :
    IsProbabilityMeasure (stateLaw law i) := by unfold stateLaw; infer_instance

theorem stateLaw_true {t : ℕ} (law : CoinLaw t) (i : Fin t) :
    (stateLaw law i).real {true} = law.rate i := by
  rw [measureReal_def, stateLaw, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp

noncomputable def rowLaw {t r n : ℕ} (law : CoinLaw t) (x : Fresh t r n) :
    Measure (Fin r → Bool) := Measure.pi (fun j => stateLaw law (x j.succ).2)

instance {t r n : ℕ} (law : CoinLaw t) (x : Fresh t r n) :
    IsProbabilityMeasure (rowLaw law x) := by unfold rowLaw; infer_instance

noncomputable def fieldLaw {t r n L : ℕ} (law : CoinLaw t) (s : Fin L → Fresh t r n) :
    Measure (Fields r L) := Measure.pi (fun i => rowLaw law (s i))

instance {t r n L : ℕ} (law : CoinLaw t) (s : Fin L → Fresh t r n) :
    IsProbabilityMeasure (fieldLaw law s) := by unfold fieldLaw; infer_instance

end SatKUpper.Sampling
