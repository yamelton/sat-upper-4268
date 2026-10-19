import SatUpper.FiniteUniformLaw
import SatUpper.Ground.Minimum
import Mathlib.Algebra.Order.Floor.Ring

/-! Uniform k-SAT, with and without distinct variable positions.
The target probability uses finite cardinalities and is defined also for
the finitely many n<k at which no legal clause exists. -/

open MeasureTheory

namespace SatKUpper.Model

abbrev Assignment (n : ℕ) := Fin n → Bool
abbrev Clause (k n : ℕ) := Fin k → Fin n × Bool
abbrev Formula (k n M : ℕ) := Fin M → Clause k n
abbrev LegalClause (k n : ℕ) := {c : Clause k n // Function.Injective (fun j => (c j).1)}
abbrev LegalFormula (k n M : ℕ) := Fin M → LegalClause k n

abbrev Violates {k n : ℕ} (σ : Assignment n) (c : Clause k n) : Prop :=
  ∀ j, σ (c j).1 = (c j).2

def Satisfiable {k n M : ℕ} (F : Formula k n M) : Prop :=
  ∃ σ : Assignment n, ∀ i, ¬ Violates σ (F i)

def forget {k n M : ℕ} (F : LegalFormula k n M) : Formula k n M := fun i => (F i).val

noncomputable def satisfiabilityProbability (k n M : ℕ) : ℝ := by
  classical
  exact ((Finset.univ.filter (fun F : LegalFormula k n M => Satisfiable (forget F))).card : ℝ) /
    (Fintype.card (LegalFormula k n M) : ℝ)

def UpperBound (k : ℕ) (α : ℝ) : Prop :=
  Filter.Tendsto (fun n => satisfiabilityProbability k n ⌊α*(n : ℝ)⌋₊)
    Filter.atTop (nhds 0)

noncomputable def cost {k n M : ℕ} (F : Formula k n M) (σ : Assignment n) : ℕ :=
  ∑ i, if Violates σ (F i) then 1 else 0

noncomputable def energy {k n M : ℕ} (F : Formula k n M) : ℕ :=
  SatUpper.GroundMinimum.value (cost F)

noncomputable def mean (k n M : ℕ) : ℝ :=
  SatUpper.uniformAverage (fun F : Formula k n M => (energy F : ℝ))

noncomputable def variance (k n M : ℕ) : ℝ :=
  SatUpper.uniformVariance (fun F : Formula k n M => (energy F : ℝ))

noncomputable def clauseLaw (k n : ℕ) : Measure (Clause k n) :=
  SatUpper.FiniteUniformLaw.law (Clause k n)

instance (k n : ℕ) [NeZero n] : IsProbabilityMeasure (clauseLaw k n) := by
  unfold clauseLaw
  infer_instance

theorem clause_family_integral (k n M : ℕ) [NeZero n] (f : Formula k n M → ℝ) :
    (∫ F, f F ∂Measure.pi (fun _ => clauseLaw k n)) = SatUpper.uniformAverage f := by
  rw [clauseLaw, SatUpper.FiniteUniformLaw.pi_law, SatUpper.FiniteUniformLaw.integral_law]

theorem energy_zero_of_satisfiable {k n M : ℕ} {F : Formula k n M}
    (h : Satisfiable F) : energy F = 0 := by
  obtain ⟨σ,hσ⟩ := h
  apply Nat.eq_zero_of_le_zero ((SatUpper.GroundMinimum.value_le (cost F) σ).trans ?_)
  have hc : cost F σ = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact if_neg (hσ i)
  exact hc.le

theorem cost_one_clause {k n M : ℕ} (F G : Formula k n M) (j : Fin M)
    (hFG : ∀ i, i ≠ j → F i = G i) (σ : Assignment n) : cost F σ ≤ cost G σ + 1 := by
  classical
  have he : ∑ i ∈ Finset.univ.erase j, (if Violates σ (F i) then 1 else 0 : ℕ) =
      ∑ i ∈ Finset.univ.erase j, (if Violates σ (G i) then 1 else 0 : ℕ) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hFG i (Finset.mem_erase.mp hi).1]
  unfold cost
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ j), he]
  split_ifs <;> omega

theorem energy_one_clause_lipschitz {k n M : ℕ} (F G : Formula k n M) (j : Fin M)
    (hFG : ∀ i, i ≠ j → F i = G i) : |(energy F : ℝ) - energy G| ≤ 1 := by
  have hf : energy F ≤ energy G + 1 := by
    obtain ⟨σ,hσ⟩ := SatUpper.GroundMinimum.attained (cost G)
    exact (SatUpper.GroundMinimum.value_le (cost F) σ).trans
      (by simpa [hσ, energy] using cost_one_clause F G j hFG σ)
  have hg : energy G ≤ energy F + 1 := by
    obtain ⟨σ,hσ⟩ := SatUpper.GroundMinimum.attained (cost F)
    exact (SatUpper.GroundMinimum.value_le (cost G) σ).trans
      (by simpa [hσ, energy] using cost_one_clause G F j (fun i hi => (hFG i hi).symm) σ)
  have hf' : (energy F : ℝ) ≤ energy G + 1 := by exact_mod_cast hf
  have hg' : (energy G : ℝ) ≤ energy F + 1 := by exact_mod_cast hg
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end SatKUpper.Model
