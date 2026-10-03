import Mathlib.Data.Fintype.Pi

/-! Group site warnings by variable and literal sign. -/

namespace SatUpper.SiteVertexIdentity

variable {n L : ℕ}

abbrev Side (u : Fin L → Fin 3 → Fin n × Bool) (v : Fin n) (b : Bool) :=
  {i : Fin L // (u i 0).1 = v ∧ (u i 0).2 = b}

def messages (u : Fin L → Fin 3 → Fin n × Bool) (v : Fin n) (b : Bool)
    (x : (Fin L × Fin 3) → Bool) (i : Side u v b) : Bool × Bool :=
  (x (i.1,1),x (i.1,2))

end SatUpper.SiteVertexIdentity
