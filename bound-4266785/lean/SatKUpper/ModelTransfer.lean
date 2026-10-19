import SatKUpper.LegalCounting
import SatKUpper.Variance

/-! Positive linear mean energy forces unsatisfiability in the legal k-SAT model. -/

namespace SatKUpper.ModelTransfer

theorem forget_injective {k n M : ℕ} :
    Function.Injective (Model.forget (k := k) (n := n) (M := M)) := by
  intro F G h
  funext i
  apply Subtype.ext
  exact congrFun h i

theorem satisfiabilityProbability_le_variance {k n M : ℕ} (hn : 2*k+1 ≤ n) {α : ℝ}
    (hM : (M : ℝ) ≤ α*n) (hmean : 0 < Model.mean k n M) :
    Model.satisfiabilityProbability k n M ≤
      Real.exp (2*(k : ℝ)^2*α) * (Model.variance k n M / (Model.mean k n M)^2) := by
  classical
  letI : NeZero n := ⟨by omega⟩
  let event := Finset.univ.filter (fun F : Model.LegalFormula k n M => Model.Satisfiable (Model.forget F))
  let zero := Finset.univ.filter (fun F : Model.Formula k n M => Model.energy F = 0)
  have hi : event.image Model.forget ⊆ zero := by
    intro F hF
    obtain ⟨G,hG,rfl⟩ := Finset.mem_image.mp hF
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      Model.energy_zero_of_satisfiable (Finset.mem_filter.mp hG).2⟩
  have hcard : (event.card : ℝ) ≤ zero.card := by
    exact_mod_cast (by
      simpa only [Finset.card_image_of_injective _ forget_injective] using
        Finset.card_le_card hi)
  have hz := SatUpper.finite_event_chebyshev (fun F : Model.Formula k n M => (Model.energy F : ℝ))
    zero hmean.ne' (fun F hF => by simp only [(Finset.mem_filter.mp hF).2, Nat.cast_zero])
  have hnonneg : 0 ≤ (zero.card : ℝ) / Fintype.card (Model.Formula k n M) := by positivity
  calc
    Model.satisfiabilityProbability k n M ≤ (zero.card : ℝ) / Fintype.card (Model.LegalFormula k n M) :=
      div_le_div_of_nonneg_right hcard (Nat.cast_nonneg _)
    _ = ((Fintype.card (Model.Formula k n M) : ℝ) / Fintype.card (Model.LegalFormula k n M)) *
        ((zero.card : ℝ) / Fintype.card (Model.Formula k n M)) := by
      have hc : (Fintype.card (Model.Formula k n M) : ℝ) ≠ 0 := by
        exact_mod_cast Fintype.card_ne_zero
      field_simp
    _ ≤ Real.exp (2*(k : ℝ)^2*α) * ((zero.card : ℝ) / Fintype.card (Model.Formula k n M)) :=
      mul_le_mul_of_nonneg_right (LegalCounting.formula_ratio_le hn hM) hnonneg
    _ ≤ _ := mul_le_mul_of_nonneg_left hz (Real.exp_pos _).le

/-- A positive linear expected minimum suffices; the variance bound is already proved. -/
theorem upperBound_of_linear_mean (k : ℕ) {α c : ℝ} (hα : 0 ≤ α) (hc : 0 < c)
    (hmean : ∀ᶠ n in Filter.atTop, c*n ≤ Model.mean k n ⌊α*(n : ℝ)⌋₊) :
    Model.UpperBound k α := by
  unfold Model.UpperBound
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => by
    unfold Model.satisfiabilityProbability
    positivity))
  · filter_upwards [hmean, Filter.eventually_ge_atTop (2*k+1)] with n hm hn
    letI : NeZero n := ⟨by omega⟩
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    have hcount : (⌊α*(n : ℝ)⌋₊ : ℝ) ≤ α*n :=
      Nat.floor_le (mul_nonneg hα hn0.le)
    have hvar : Model.variance k n ⌊α*(n : ℝ)⌋₊ ≤ α*n :=
      (Variance.energy_variance_le k n _).trans hcount
    have hcn : 0 < c*n := mul_pos hc hn0
    have hm0 : 0 < Model.mean k n ⌊α*(n : ℝ)⌋₊ := hcn.trans_le hm
    have hsq := pow_le_pow_left₀ hcn.le hm 2
    calc
      Model.satisfiabilityProbability k n ⌊α*(n : ℝ)⌋₊ ≤
          Real.exp (2*(k : ℝ)^2*α) * (Model.variance k n ⌊α*(n : ℝ)⌋₊ /
            (Model.mean k n ⌊α*(n : ℝ)⌋₊)^2) :=
        satisfiabilityProbability_le_variance hn hcount hm0
      _ ≤ Real.exp (2*(k : ℝ)^2*α) * (α*n / (c*n)^2) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact (div_le_div_of_nonneg_right hvar (sq_nonneg _)).trans
          (div_le_div_of_nonneg_left (mul_nonneg hα hn0.le) (sq_pos_of_pos hcn) hsq)
      _ = (Real.exp (2*(k : ℝ)^2*α)*α/c^2)/(n : ℝ) := by field_simp
  · exact tendsto_const_div_atTop_nhds_zero_nat (Real.exp (2*(k : ℝ)^2*α)*α/c^2)

end SatKUpper.ModelTransfer
