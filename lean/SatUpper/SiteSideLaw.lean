import SatUpper.SiteMessageLaw
import SatUpper.TrialVertex

/-! The two finite sign sides have exactly the independent trial vertex law. -/

open MeasureTheory
open SatUpper.SiteVertexIdentity

namespace SatUpper.SiteSideLaw

variable {n L : ℕ}

def selectIndex (u : Fin L → Fin 3 → Fin n × Bool) (v : Fin n) :
    Side u v true ⊕ Side u v false → Fin L := Sum.elim Subtype.val Subtype.val

theorem selectIndex_injective (u : Fin L → Fin 3 → Fin n × Bool) (v : Fin n) :
    Function.Injective (selectIndex u v) := by
  apply Subtype.val_injective.sumElim Subtype.val_injective
  intro a b h
  have := a.2.2
  rw [h, b.2.2] at this
  cases this

noncomputable def surveys (u : Fin L → Fin 3 → Fin n × Bool) (v : Fin n) (b : Bool)
    (q : (Fin L × Fin 3) → Fin 4) (i : Side u v b) : WitnessVertex.Mark :=
  (q (i.1,1),q (i.1,2))

def jointIndex (u : Fin L → Fin 3 → Fin n × Bool) :
    (Σ v, Side u v true ⊕ Side u v false) → Fin L := fun z => selectIndex u z.1 z.2

theorem jointIndex_injective (u : Fin L → Fin 3 → Fin n × Bool) :
    Function.Injective (jointIndex u) := by
  have hv (z : Σ v, Side u v true ⊕ Side u v false) : (u (jointIndex u z) 0).1 = z.1 := by
    rcases z with ⟨v, a | a⟩ <;> exact a.2.1
  rintro ⟨v,a⟩ ⟨w,b⟩ h
  have he : v = w := (hv ⟨v,a⟩).symm.trans ((congrArg (fun i => (u i 0).1) h).trans (hv ⟨w,b⟩))
  subst w
  exact congrArg (Sigma.mk v) (selectIndex_injective u v h)

/-- Regroup all messages at once: distinct signed variables use disjoint coordinates. -/
theorem joint_law (u : Fin L → Fin 3 → Fin n × Bool) (q : (Fin L × Fin 3) → Fin 4) :
    Measure.map (fun x : (Fin L × Fin 3) → Bool =>
      fun v => (messages u v true x, messages u v false x))
      (Measure.pi (fun j => TrialFields.stateLaw (q j))) =
      Measure.pi (fun v => TrialVertex.innerLaw (surveys u v true q) (surveys u v false q)) := by
  let μ (i : Fin L) := TrialFields.messageLaw (q (i,1),q (i,2))
  have hs := FiniteCoordinateSelection.select_law μ (jointIndex u) (jointIndex_injective u)
  dsimp only [jointIndex] at hs
  have hc := (ProductMeasures.piCurry (fun v i => μ (selectIndex u v i))).map_eq
  rw [← hs, Measure.map_map (by fun_prop) (by fun_prop)] at hc
  have hp := Measure.pi_map_pi (μ := fun v => Measure.pi (fun i => μ (selectIndex u v i)))
    (f := fun v => MeasurableEquiv.sumPiEquivProdPi
      (fun _ : Side u v true ⊕ Side u v false => TrialFields.InnerMark))
    (fun _ => (MeasurableEquiv.measurable _).aemeasurable)
  simp only [(measurePreserving_sumPiEquivProdPi _).map_eq] at hp
  rw [← hc, Measure.map_map (by fun_prop) (by fun_prop),
    ← SiteMessageLaw.message_arrays_law q, Measure.map_map (by fun_prop) (by fun_prop)] at hp
  exact hp

end SatUpper.SiteSideLaw
