import SatUpper.Ground.Formula
import SatUpper.FiniteVariance
import Mathlib.Data.Fintype.CardEmbedding

/-! Conditioning on distinct variables costs only a constant factor in probability. -/

namespace SatUpper.LegalConditioning

theorem card_clause (n : ℕ) : Fintype.card (Clause n) = n.descFactorial 3 * 8 := by
  let e : {v : Fin 3 → Fin n // Function.Injective v} ≃ (Fin 3 ↪ Fin n) :=
    ⟨fun v => ⟨v.val,v.property⟩, fun v => ⟨v.toFun,v.injective⟩, fun _ => rfl, fun _ => rfl⟩
  simp only [Clause, Fintype.card_prod, Fintype.card_congr e,
    Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fun, Fintype.card_bool]
  norm_num

theorem clause_ratio (n : ℕ) (hn : 6 ≤ n) :
    (Fintype.card (ClauseEndpoint.Clause n) : ℝ) / Fintype.card (Clause n) =
      (n : ℝ)^2 / (((n : ℝ)-1)*((n : ℝ)-2)) := by
  have hn₁ : 1 ≤ n := by omega
  have hn₂ : 2 ≤ n := by omega
  have hn₀ : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [card_clause]
  simp only [ClauseEndpoint.Clause, Fintype.card_fun, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_bool, Nat.descFactorial_succ, Nat.descFactorial_zero,
    Nat.sub_zero, mul_one]
  push_cast
  rw [Nat.cast_sub hn₁, Nat.cast_sub hn₂]
  push_cast
  field_simp
  ring

theorem ratio_le_exp (n : ℕ) (hn : 6 ≤ n) :
    (Fintype.card (ClauseEndpoint.Clause n) : ℝ) / Fintype.card (Clause n) ≤
      Real.exp (6/(n : ℝ)) := by
  rw [clause_ratio n hn]
  have hn' : (6 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 < ((n : ℝ)-1)*((n : ℝ)-2) := mul_pos (by linarith) (by linarith)
  have hr : 0 < (n : ℝ)^2 / (((n : ℝ)-1)*((n : ℝ)-2)) := div_pos (by positivity) hp
  have hb : (n : ℝ)^2 / (((n : ℝ)-1)*((n : ℝ)-2)) - 1 ≤ 6/(n : ℝ) := by
    apply (le_div_iff₀ (by linarith : (0 : ℝ) < n)).mpr
    rw [sub_mul, div_mul_eq_mul_div]
    rw [sub_le_iff_le_add]
    apply (div_le_iff₀ hp).mpr
    simp only [one_mul]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ n) (by linarith : (0 : ℝ) ≤ n-6)]
  have h := Real.exp_le_exp.mpr ((Real.log_le_sub_one_of_pos hr).trans hb)
  simpa [Real.exp_log hr] using h

theorem formula_ratio_le {n M : ℕ} (hn : 6 ≤ n) {α : ℝ} (hM : (M : ℝ) ≤ α*n) :
    (Fintype.card (GroundFormula.Formula n M) : ℝ) / Fintype.card (Formula n M) ≤
      Real.exp (6*α) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  calc
    _ = ((Fintype.card (ClauseEndpoint.Clause n) : ℝ) / Fintype.card (Clause n))^M := by
      simp only [GroundFormula.Formula, Formula, Fintype.card_fun, Fintype.card_fin,
        Nat.cast_pow, div_pow]
    _ ≤ (Real.exp (6/(n : ℝ)))^M :=
      pow_le_pow_left₀ (by positivity) (ratio_le_exp n hn) M
    _ = Real.exp ((M : ℝ)*(6/(n : ℝ))) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (6*α) := by
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_right hM (by positivity : 0 ≤ 6/(n : ℝ))
      have he : (α*n)*(6/(n : ℝ)) = 6*α := by field_simp
      rwa [he] at h

theorem satisfiabilityProbability_le_variance {n M : ℕ} (hn : 6 ≤ n) {α : ℝ}
    (hM : (M : ℝ) ≤ α*n) (hmean : 0 < GroundFormula.mean n M) :
    satisfiabilityProbability n M ≤
      Real.exp (6*α) * (GroundFormula.variance n M / (GroundFormula.mean n M)^2) := by
  classical
  letI : NeZero n := ⟨by omega⟩
  let event := Finset.univ.filter (fun F : Formula n M => Satisfiable F)
  let zero := Finset.univ.filter (fun F : GroundFormula.Formula n M => GroundFormula.energy F = 0)
  have hi : event.image GroundFormula.clauses ⊆ zero := by
    intro F hF
    obtain ⟨G,hG,rfl⟩ := Finset.mem_image.mp hF
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      GroundFormula.energy_zero_of_satisfiable (Finset.mem_filter.mp hG).2⟩
  have hcard : (event.card : ℝ) ≤ zero.card := by
    exact_mod_cast (by
      simpa only [Finset.card_image_of_injective _ GroundFormula.clauses_injective] using
        Finset.card_le_card hi)
  have hz := finite_event_chebyshev (fun F : GroundFormula.Formula n M => (GroundFormula.energy F : ℝ))
    zero hmean.ne' (fun F hF => by simp only [(Finset.mem_filter.mp hF).2, Nat.cast_zero])
  have hnonneg : 0 ≤ (zero.card : ℝ) / Fintype.card (GroundFormula.Formula n M) := by positivity
  calc
    satisfiabilityProbability n M ≤ (zero.card : ℝ) / Fintype.card (Formula n M) :=
      div_le_div_of_nonneg_right hcard (Nat.cast_nonneg _)
    _ = ((Fintype.card (GroundFormula.Formula n M) : ℝ) / Fintype.card (Formula n M)) *
        ((zero.card : ℝ) / Fintype.card (GroundFormula.Formula n M)) := by
      have hc : (Fintype.card (GroundFormula.Formula n M) : ℝ) ≠ 0 := by
        exact_mod_cast Fintype.card_ne_zero
      field_simp
    _ ≤ Real.exp (6*α) * ((zero.card : ℝ) / Fintype.card (GroundFormula.Formula n M)) :=
      mul_le_mul_of_nonneg_right (formula_ratio_le hn hM) hnonneg
    _ ≤ _ := mul_le_mul_of_nonneg_left hz (Real.exp_pos _).le

/-- A positive linear minimum-energy mean and linear variance force unsatisfiability,
even after conditioning every clause to use distinct variables. -/
theorem candidate_of_mean_and_variance_bounds (α c V : ℝ)
    (hc : 0 < c) (hV : 0 ≤ V)
    (hcount : ∀ n, (clauseCount n : ℝ) ≤ α*n)
    (hmean : ∀ᶠ n in Filter.atTop, c*n ≤ GroundFormula.mean n (clauseCount n))
    (hvar : ∀ᶠ n in Filter.atTop, GroundFormula.variance n (clauseCount n) ≤ V*n) :
    CandidateUpperBound := by
  unfold CandidateUpperBound
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => by
    unfold satisfiabilityProbability
    positivity))
  · filter_upwards [hmean, hvar, Filter.eventually_ge_atTop 6] with n hm hv hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hcn : 0 < c*n := mul_pos hc hn0
    have hm0 : 0 < GroundFormula.mean n (clauseCount n) := hcn.trans_le hm
    have hsq := pow_le_pow_left₀ hcn.le hm 2
    calc
      satisfiabilityProbability n (clauseCount n) ≤
          Real.exp (6*α) * (GroundFormula.variance n (clauseCount n) /
            (GroundFormula.mean n (clauseCount n))^2) :=
        satisfiabilityProbability_le_variance hn (hcount n) hm0
      _ ≤ Real.exp (6*α) * (V*n / (c*n)^2) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact (div_le_div_of_nonneg_right hv (sq_nonneg _)).trans
          (div_le_div_of_nonneg_left (mul_nonneg hV hn0.le) (sq_pos_of_pos hcn) hsq)
      _ = (Real.exp (6*α)*V/c^2)/(n : ℝ) := by field_simp
  · exact tendsto_const_div_atTop_nhds_zero_nat (Real.exp (6*α)*V/c^2)

end SatUpper.LegalConditioning
