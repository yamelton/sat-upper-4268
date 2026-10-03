import SatUpper.FiniteCoordinateSelection
import SatUpper.TrialFields

/-! The two used cavity coordinates at each site have the trial message law. -/

open MeasureTheory

namespace SatUpper.SiteMessageLaw

variable {L : ℕ}

def coordinate (j : Fin L × Fin 2) : Fin L × Fin 3 := (j.1, j.2.castSucc + 1)

theorem coordinate_injective : Function.Injective (coordinate (L := L)) := by
  intro a b h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  dsimp [coordinate] at h1 h2
  have h3 : a.2 = b.2 := by
    have hv := congrArg Fin.val h2
    rcases a with ⟨a,i⟩
    rcases b with ⟨b,j⟩
    fin_cases i <;> fin_cases j <;> simp_all
  exact Prod.ext h1 h3

theorem message_arrays_law (q : (Fin L × Fin 3) → Fin 4) :
    Measure.map (fun x : (Fin L × Fin 3) → Bool => fun i => (x (i,1),x (i,2)))
      (Measure.pi (fun j => TrialFields.stateLaw (q j))) =
      Measure.pi (fun i => TrialFields.messageLaw (q (i,1),q (i,2))) := by
  have hs := FiniteCoordinateSelection.select_law (fun j => TrialFields.stateLaw (q j))
    coordinate coordinate_injective
  have hp := FiniteCoordinateSelection.pair_law
    (fun (i : Fin L) (j : Fin 2) => TrialFields.stateLaw (q (coordinate (i,j))))
  rw [← hs, Measure.map_map (by fun_prop) (by fun_prop)] at hp
  exact hp

end SatUpper.SiteMessageLaw
