import SatKUpper.SiteVertex
import SatUpper.FiniteCoordinateSelection

/-! Regroup independent warning rows at their retained variables. A conflict
at a variable forces at least one violation, uniformly in the clause size. -/

open MeasureTheory SatKUpper.Sampling SatKUpper.Ground SatKUpper.SiteVertex SatUpper

namespace SatKUpper.SiteGround

variable {t r n L : ℕ}

abbrev Side (s : Fin L → Fresh t r n) (v : Fin n) (b : Bool) :=
  {i : Fin L // (s i 0).1.1 = v ∧ (s i 0).1.2 = b}

def messages (s : Fin L → Fresh t r n) (v : Fin n) (b : Bool)
    (x : Fields r L) (i : Side s v b) : Message r := x i.val

def surveys (s : Fin L → Fresh t r n) (v : Fin n) (b : Bool)
    (i : Side s v b) : Mark t r := fun j => (s i.val j.succ).2

def selectIndex (s : Fin L → Fresh t r n) (v : Fin n) :
    Side s v true ⊕ Side s v false → Fin L := Sum.elim Subtype.val Subtype.val

theorem selectIndex_injective (s : Fin L → Fresh t r n) (v : Fin n) :
    Function.Injective (selectIndex s v) := by
  apply Subtype.val_injective.sumElim Subtype.val_injective
  intro a b h
  have := a.2.2
  rw [h, b.2.2] at this
  cases this

def jointIndex (s : Fin L → Fresh t r n) :
    (Σ v, Side s v true ⊕ Side s v false) → Fin L := fun z => selectIndex s z.1 z.2

theorem jointIndex_injective (s : Fin L → Fresh t r n) :
    Function.Injective (jointIndex s) := by
  have hv (z : Σ v, Side s v true ⊕ Side s v false) :
      (s (jointIndex s z) 0).1.1 = z.1 := by
    rcases z with ⟨v, a | a⟩ <;> exact a.2.1
  rintro ⟨v,a⟩ ⟨w,b⟩ h
  have he : v = w := (hv ⟨v,a⟩).symm.trans
    ((congrArg (fun i => (s i 0).1.1) h).trans (hv ⟨w,b⟩))
  subst w
  exact congrArg (Sigma.mk v) (selectIndex_injective s v h)

theorem joint_law (law : CoinLaw t) (s : Fin L → Fresh t r n) :
    Measure.map (fun x : Fields r L =>
      fun v => (messages s v true x, messages s v false x)) (fieldLaw law s) =
      Measure.pi (fun v => innerLaw law (surveys s v true) (surveys s v false)) := by
  let μ (i : Fin L) := rowLaw law (s i)
  have hs := FiniteCoordinateSelection.select_law μ (jointIndex s) (jointIndex_injective s)
  dsimp only [jointIndex] at hs
  have hc := (ProductMeasures.piCurry (fun v i => μ (selectIndex s v i))).map_eq
  rw [← hs, Measure.map_map (by fun_prop) (by fun_prop)] at hc
  have hp := Measure.pi_map_pi (μ := fun v => Measure.pi (fun i => μ (selectIndex s v i)))
    (f := fun v => MeasurableEquiv.sumPiEquivProdPi
      (fun _ : Side s v true ⊕ Side s v false => Message r))
    (fun _ => (MeasurableEquiv.measurable _).aemeasurable)
  simp only [(measurePreserving_sumPiEquivProdPi _).map_eq] at hp
  rw [← hc, Measure.map_map (by fun_prop) (by fun_prop)] at hp
  exact hp

noncomputable def localCost (s : Fin L → Fresh t r n) (x : Fields r L)
    (v : Fin n) (b : Bool) : ℕ :=
  ∑ i, if (s i 0).1.1 = v then
    if b = (s i 0).1.2 ∧ (∀ j, x i j = true) then 1 else 0 else 0

theorem cost_eq_sum (s : Fin L → Fresh t r n) (x : Fields r L) (σ : Spin n) :
    cost Fin.elim0 s x σ = ∑ v, localCost s x v (σ v) := by
  classical
  unfold localCost
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp [cost]

theorem conflict_le (s : Fin L → Fresh t r n) (x : Fields r L)
    (v : Fin n) (b : Bool) :
    conflict (messages s v true x, messages s v false x) ≤ localCost s x v b := by
  classical
  unfold conflict
  split
  · exact Nat.zero_le _
  · rename_i h
    obtain ⟨ht,hf⟩ := bad_event_warnings h
    have hw : ∃ i : Side s v b, messages s v b x i = fun _ => true := by
      cases b <;> assumption
    obtain ⟨i,hi⟩ := hw
    have hs := Finset.single_le_sum (f := fun i : Fin L =>
      if (s i 0).1.1 = v then if b = (s i 0).1.2 ∧ (∀ j, x i j = true)
        then 1 else 0 else 0) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i.val)
    have hj : ∀ j, x i.val j = true := fun j => congrFun hi j
    simpa [localCost, i.property.1, i.property.2, hj] using hs

theorem conflicts_le_energy (s : Fin L → Fresh t r n) (x : Fields r L) :
    (∑ v, conflict (messages s v true x, messages s v false x)) ≤
      energy Fin.elim0 s x := by
  apply GroundMinimum.le_value
  intro σ
  rw [cost_eq_sum]
  exact Finset.sum_le_sum (fun v _ => conflict_le s x v (σ v))

theorem entropy_le (law : CoinLaw t) {y : ℝ} (hy : 0 ≤ y) (s : Fin L → Fresh t r n) :
    entropy law y Fin.elim0 s ≤ ∑ v : Fin n,
      Real.log (∫ x, Real.exp (-y * conflict x) ∂innerLaw law
        (surveys s v true) (surveys s v false)) := by
  have hb (x : Fields r L) :
      Real.exp (-y * energy Fin.elim0 s x) ≤
      ∏ v, Real.exp (-y * conflict (messages s v true x, messages s v false x)) := by
    rw [← Real.exp_sum]
    simp only [← Finset.mul_sum, ← Nat.cast_sum]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left
      (by exact_mod_cast conflicts_le_energy s x) (neg_nonpos.mpr hy))
  have h := integral_mono (μ := fieldLaw law s) Integrable.of_finite Integrable.of_finite hb
  have hf : (∫ x : Fields r L,
      ∏ v, Real.exp (-y * conflict (messages s v true x, messages s v false x))
        ∂fieldLaw law s) =
      ∏ v, ∫ x, Real.exp (-y * conflict x) ∂innerLaw law
        (surveys s v true) (surveys s v false) := by
    rw [← integral_fintype_prod_eq_prod, ← joint_law law s,
      integral_map (measurable_of_countable _).aemeasurable
        (measurable_of_countable _).aestronglyMeasurable]
  rw [hf] at h
  have hl := Real.log_le_log (moment_pos law y Fin.elim0 s) h
  rwa [Real.log_prod _ _ (fun v _ => (integral_exp_pos (μ := innerLaw law
    (surveys s v true) (surveys s v false)) Integrable.of_finite).ne')] at hl

end SatKUpper.SiteGround
