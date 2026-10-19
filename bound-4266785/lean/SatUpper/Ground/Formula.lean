import SatUpper.ClauseEndpoint
import SatUpper.Ground.Minimum
import SatUpper.Concentration

/-! Minimum violations for clauses sampled with replacement. -/

namespace SatUpper.GroundFormula

abbrev Formula (n M : ℕ) := Fin M → ClauseEndpoint.Clause n

noncomputable def cost {n M : ℕ} (F : Formula n M) (σ : Assignment n) : ℕ :=
  ∑ i, if ∀ j, σ (F i j).1 = (F i j).2 then 1 else 0

noncomputable def energy {n M : ℕ} (F : Formula n M) : ℕ := GroundMinimum.value (cost F)

noncomputable def mean (n M : ℕ) : ℝ :=
  uniformAverage (fun F : Formula n M => (energy F : ℝ))

noncomputable def variance (n M : ℕ) : ℝ :=
  uniformVariance (fun F : Formula n M => (energy F : ℝ))

def clauses {n M : ℕ} (F : SatUpper.Formula n M) : Formula n M :=
  fun i j => ((F i).1.val j, (F i).2 j)

theorem clauses_injective {n M : ℕ} : Function.Injective (clauses (n := n) (M := M)) := by
  intro F G h
  funext i
  apply Prod.ext
  · apply Subtype.ext
    funext j
    exact congrArg Prod.fst (congrFun (congrFun h i) j)
  · funext j
    exact congrArg Prod.snd (congrFun (congrFun h i) j)

theorem energy_zero_of_satisfiable {n M : ℕ} {F : SatUpper.Formula n M}
    (h : Satisfiable F) : energy (clauses F) = 0 := by
  obtain ⟨σ,hσ⟩ := h
  apply Nat.eq_zero_of_le_zero ((GroundMinimum.value_le (cost (clauses F)) σ).trans ?_)
  have hc : cost (clauses F) σ = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact if_neg (hσ i)
  exact hc.le

theorem cost_one_clause {n M : ℕ} (F G : Formula n M) (j : Fin M)
    (hFG : ∀ i, i ≠ j → F i = G i) (σ : Assignment n) : cost F σ ≤ cost G σ + 1 := by
  classical
  have he : ∑ i ∈ Finset.univ.erase j, (if ∀ k, σ (F i k).1 = (F i k).2 then 1 else 0 : ℕ) =
      ∑ i ∈ Finset.univ.erase j, (if ∀ k, σ (G i k).1 = (G i k).2 then 1 else 0 : ℕ) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hFG i (Finset.mem_erase.mp hi).1]
  unfold cost
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ j), he]
  split_ifs <;> omega

theorem energy_one_clause_lipschitz {n M : ℕ} (F G : Formula n M) (j : Fin M)
    (hFG : ∀ i, i ≠ j → F i = G i) : |(energy F : ℝ) - energy G| ≤ 1 := by
  have hf : energy F ≤ energy G + 1 := by
    obtain ⟨σ,hσ⟩ := GroundMinimum.attained (cost G)
    exact (GroundMinimum.value_le (cost F) σ).trans (by simpa [hσ, energy] using cost_one_clause F G j hFG σ)
  have hg : energy G ≤ energy F + 1 := by
    obtain ⟨σ,hσ⟩ := GroundMinimum.attained (cost F)
    exact (GroundMinimum.value_le (cost G) σ).trans (by simpa [hσ, energy] using cost_one_clause G F j (fun i hi => (hFG i hi).symm) σ)
  have hf' : (energy F : ℝ) ≤ energy G + 1 := by exact_mod_cast hf
  have hg' : (energy G : ℝ) ≤ energy F + 1 := by exact_mod_cast hg
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end SatUpper.GroundFormula
