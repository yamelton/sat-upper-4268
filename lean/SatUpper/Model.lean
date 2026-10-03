import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Topology.Order.Basic
import SatUpper.Local

/-! The uniform random 3-SAT model and the intended final statement.

Clauses have ordered, distinct variable positions and independent Boolean
falsifying signs. Every unordered legal signed clause has exactly six such
representations. Formulas are ordered lists of independently chosen clauses;
repeated clauses are allowed. Probability is expressed as a ratio of finite
cardinalities, avoiding an implicit choice of probability measure.

For n < 3 there are no legal clauses. The ratio uses Lean's convention for
division by zero; these finitely many indices do not affect the limit.
-/

namespace SatUpper

abbrev Assignment (n : ℕ) := Fin n → Bool

abbrev Clause (n : ℕ) :=
  {v : Fin 3 → Fin n // Function.Injective v} × (Fin 3 → Bool)

abbrev Formula (n M : ℕ) := Fin M → Clause n

def Violates {n : ℕ} (σ : Assignment n) (c : Clause n) : Prop :=
  ∀ j : Fin 3, σ (c.1.val j) = c.2 j

def Satisfies {n M : ℕ} (σ : Assignment n) (F : Formula n M) : Prop :=
  ∀ i : Fin M, ¬ Violates σ (F i)

def Satisfiable {n M : ℕ} (F : Formula n M) : Prop :=
  ∃ σ : Assignment n, Satisfies σ F

noncomputable def violations {n M : ℕ} (F : Formula n M) (σ : Assignment n) : ℕ :=
  by classical exact (Finset.univ.filter (fun i => Violates σ (F i))).card

noncomputable def partition {n M : ℕ} (β : ℝ) (F : Formula n M) : ℝ :=
  ∑ σ : Assignment n, Real.exp (-β * (violations F σ : ℝ))

noncomputable def satisfiabilityProbability (n M : ℕ) : ℝ := by
  classical
  exact ((Finset.univ.filter (fun F : Formula n M => Satisfiable F)).card : ℝ) /
    (Fintype.card (Formula n M) : ℝ)

/-- Exactly floor(4.268 n), computed in natural-number arithmetic. -/
def clauseCount (n : ℕ) : ℕ := 1067 * n / 250

/-- The intended endpoint. This is a proposition, NOT a proved theorem. -/
def CandidateUpperBound : Prop :=
  Filter.Tendsto (fun n => satisfiabilityProbability n (clauseCount n))
    Filter.atTop (nhds 0)

theorem violations_eq_zero_of_satisfies {n M : ℕ} {F : Formula n M}
    {σ : Assignment n} (h : Satisfies σ F) : violations F σ = 0 := by
  classical
  unfold violations
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  exact h i (Finset.mem_filter.mp hi).2

theorem partition_pos {n M : ℕ} (β : ℝ) (F : Formula n M) :
    0 < partition β F := by
  classical
  unfold partition
  apply Finset.sum_pos
  · intro σ _
    exact Real.exp_pos _
  · exact ⟨(fun _ => false), Finset.mem_univ _⟩

theorem one_le_partition_of_satisfiable {n M : ℕ} (β : ℝ)
    {F : Formula n M} (h : Satisfiable F) : 1 ≤ partition β F := by
  classical
  obtain ⟨σ, hσ⟩ := h
  have he := violations_eq_zero_of_satisfies hσ
  have hterm := Finset.single_le_sum
    (fun τ (_ : τ ∈ (Finset.univ : Finset (Assignment n))) =>
      Real.exp_nonneg (-β * (violations F τ : ℝ))) (Finset.mem_univ σ)
  simpa [partition, he] using hterm

theorem log_partition_nonneg_of_satisfiable {n M : ℕ} (β : ℝ)
    {F : Formula n M} (h : Satisfiable F) : 0 ≤ Real.log (partition β F) :=
  Real.log_nonneg (one_le_partition_of_satisfiable β h)

theorem unsatisfiable_of_log_partition_neg {n M : ℕ} (β : ℝ)
    {F : Formula n M} (h : Real.log (partition β F) < 0) : ¬ Satisfiable F := by
  intro hs
  exact (not_lt_of_ge (log_partition_nonneg_of_satisfiable β hs)) h

theorem violations_le_of_one_clause_change {n M : ℕ}
    (F G : Formula n M) (j : Fin M)
    (hFG : ∀ i, i ≠ j → F i = G i) (σ : Assignment n) :
    violations F σ ≤ violations G σ + 1 := by
  classical
  have hsub : Finset.univ.filter (fun i => Violates σ (F i)) ⊆
      insert j (Finset.univ.filter (fun i => Violates σ (G i))) := by
    intro i hi
    by_cases hij : i = j
    · subst i
      exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      rw [Finset.mem_filter] at hi ⊢
      exact ⟨hi.1, by rw [← hFG i hij]; exact hi.2⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)

theorem partition_le_exp_mul_of_energy_le {n M : ℕ} {β : ℝ} (hβ : 0 ≤ β)
    (F G : Formula n M)
    (hE : ∀ σ, violations G σ ≤ violations F σ + 1) :
    partition β F ≤ Real.exp β * partition β G := by
  classical
  unfold partition
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro σ _
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have he : (violations G σ : ℝ) ≤ (violations F σ : ℝ) + 1 := by
    exact_mod_cast hE σ
  nlinarith [mul_nonneg hβ (sub_nonneg.mpr he)]

theorem log_partition_le_add_of_energy_le {n M : ℕ} {β : ℝ} (hβ : 0 ≤ β)
    (F G : Formula n M)
    (hE : ∀ σ, violations G σ ≤ violations F σ + 1) :
    Real.log (partition β F) ≤ β + Real.log (partition β G) := by
  have hp := partition_le_exp_mul_of_energy_le hβ F G hE
  have hl := Real.log_le_log (partition_pos β F) hp
  rw [Real.log_mul (ne_of_gt (Real.exp_pos β)) (ne_of_gt (partition_pos β G)),
    Real.log_exp] at hl
  exact hl

/-- The bounded-change hypothesis needed by a concentration argument. -/
theorem log_partition_one_clause_lipschitz {n M : ℕ} {β : ℝ} (hβ : 0 ≤ β)
    (F G : Formula n M) (j : Fin M)
    (hFG : ∀ i, i ≠ j → F i = G i) :
    |Real.log (partition β F) - Real.log (partition β G)| ≤ β := by
  have h1 := log_partition_le_add_of_energy_le hβ F G
    (violations_le_of_one_clause_change G F j (fun i hi => (hFG i hi).symm))
  have h2 := log_partition_le_add_of_energy_le hβ G F
    (violations_le_of_one_clause_change F G j hFG)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end SatUpper
