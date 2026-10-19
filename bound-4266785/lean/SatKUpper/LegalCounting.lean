import SatKUpper.Model
import Mathlib.Data.Fintype.CardEmbedding

/-! A uniform-in-n bound on the cost of conditioning k-SAT clauses to be legal. -/

namespace SatKUpper.LegalCounting

theorem card_clause (k n : ℕ) :
    Fintype.card (Model.LegalClause k n) = n.descFactorial k * 2^k := by
  classical
  let e : Model.LegalClause k n ≃ ((Fin k ↪ Fin n) × (Fin k → Bool)) :=
    { toFun := fun c => (⟨fun j => (c.val j).1,c.property⟩,fun j => (c.val j).2)
      invFun := fun p => ⟨fun j => (p.1 j,p.2 j),p.1.injective⟩
      left_inv := fun c => by apply Subtype.ext; funext j; rfl
      right_inv := fun p => by
        apply Prod.ext
        · apply Function.Embedding.ext
          intro j
          rfl
        · rfl }
  rw [Fintype.card_congr e]
  simp only [Fintype.card_prod, Fintype.card_embedding_eq, Fintype.card_fin,
    Fintype.card_fun, Fintype.card_bool]

theorem clause_ratio_le_power (k n : ℕ) (hn : 2*k+1 ≤ n) :
    (Fintype.card (Model.Clause k n) : ℝ) / Fintype.card (Model.LegalClause k n) ≤
      ((n : ℝ)/((n : ℝ)-k))^k := by
  classical
  have hkn : k ≤ n := by omega
  have hp : 0 < n-k := by omega
  have hd : (0 : ℝ) < n.descFactorial k := Nat.cast_pos.mpr (Nat.descFactorial_pos.mpr hkn)
  have hl : (n-k)^k ≤ n.descFactorial k :=
    (Nat.pow_le_pow_left (by omega : n-k ≤ n+1-k) k).trans (Nat.pow_sub_le_descFactorial n k)
  have hl' : ((n : ℝ)-k)^k ≤ (n.descFactorial k : ℝ) := by
    have hh : ((n-k : ℕ) : ℝ)^k ≤ (n.descFactorial k : ℝ) := by exact_mod_cast hl
    simpa only [Nat.cast_sub hkn] using hh
  have hnmk : (0 : ℝ) < (n : ℝ)-k := sub_pos.mpr (by exact_mod_cast (show k < n by omega))
  rw [card_clause]
  simp only [Model.Clause, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_bool, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_pow]
  calc
    _ = (n : ℝ)^k/(n.descFactorial k : ℝ) := by
      have htwo : (2 : ℝ)^k ≠ 0 := by positivity
      field_simp
    _ ≤ (n : ℝ)^k/((n : ℝ)-k)^k :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos hnmk k) hl'
    _ = _ := (div_pow _ _ _).symm

theorem ratio_le_exp (k n : ℕ) (hn : 2*k+1 ≤ n) :
    (Fintype.card (Model.Clause k n) : ℝ) / Fintype.card (Model.LegalClause k n) ≤
      Real.exp (2*(k : ℝ)^2/n) := by
  classical
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hn' : 2*(k : ℝ)+1 ≤ n := by exact_mod_cast hn
  have hd : (0 : ℝ) < (n : ℝ)-k := by linarith
  have hr : 0 < (n : ℝ)/((n : ℝ)-k) := div_pos hn0 hd
  have hb : (n : ℝ)/((n : ℝ)-k)-1 ≤ 2*(k : ℝ)/n := by
    apply (le_div_iff₀ hn0).2
    rw [sub_mul, div_mul_eq_mul_div, sub_le_iff_le_add]
    apply (div_le_iff₀ hd).2
    nlinarith [mul_nonneg (Nat.cast_nonneg k) (show (0 : ℝ) ≤ n-2*k by linarith)]
  have he := Real.exp_le_exp.mpr ((Real.log_le_sub_one_of_pos hr).trans hb)
  have hb' : (n : ℝ)/((n : ℝ)-k) ≤ Real.exp (2*(k : ℝ)/n) := by
    simpa only [Real.exp_log hr] using he
  calc
    _ ≤ ((n : ℝ)/((n : ℝ)-k))^k := clause_ratio_le_power k n hn
    _ ≤ (Real.exp (2*(k : ℝ)/n))^k := pow_le_pow_left₀ hr.le hb' k
    _ = Real.exp (2*(k : ℝ)^2/n) := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem formula_ratio_le {k n M : ℕ} (hn : 2*k+1 ≤ n) {α : ℝ}
    (hM : (M : ℝ) ≤ α*n) :
    (Fintype.card (Model.Formula k n M) : ℝ) / Fintype.card (Model.LegalFormula k n M) ≤
      Real.exp (2*(k : ℝ)^2*α) := by
  classical
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  calc
    _ = ((Fintype.card (Model.Clause k n) : ℝ) / Fintype.card (Model.LegalClause k n))^M := by
      simp only [Model.Formula, Model.LegalFormula, Fintype.card_fun, Fintype.card_fin,
        Nat.cast_pow, div_pow]
    _ ≤ (Real.exp (2*(k : ℝ)^2/n))^M :=
      pow_le_pow_left₀ (by positivity) (ratio_le_exp k n hn) M
    _ = Real.exp ((M : ℝ)*(2*(k : ℝ)^2/n)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (2*(k : ℝ)^2*α) := by
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_right hM (by positivity : 0 ≤ 2*(k : ℝ)^2/n)
      have he : (α*n)*(2*(k : ℝ)^2/n) = 2*(k : ℝ)^2*α := by field_simp
      rwa [he] at h

end SatKUpper.LegalCounting
