import SatUpper.Model
import Mathlib.Analysis.SpecificLimits.Basic

/-! Finite-sample Chebyshev reduction from mean and variance bounds.

A linear variance bound suffices for the asymptotic conclusion. The bound
is derived from the one-clause Lipschitz theorem in `VarianceControl.lean`.
-/

namespace SatUpper

noncomputable def uniformAverage {Ω : Type*} [Fintype Ω] (X : Ω → ℝ) : ℝ :=
  (∑ ω, X ω) / (Fintype.card Ω : ℝ)

noncomputable def uniformVariance {Ω : Type*} [Fintype Ω] (X : Ω → ℝ) : ℝ :=
  uniformAverage (fun ω => (X ω - uniformAverage X) ^ 2)

theorem finite_event_chebyshev {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) (event : Finset Ω) {center : ℝ} (hc : center ≠ 0)
    (hevent : ∀ ω ∈ event, X ω = 0) :
    (event.card : ℝ) / (Fintype.card Ω : ℝ) ≤
      uniformAverage (fun ω => (X ω - center) ^ 2) / center ^ 2 := by
  classical
  have hcard : (0 : ℝ) < Fintype.card Ω := by
    exact_mod_cast Fintype.card_pos
  have hc2 : 0 < center ^ 2 := sq_pos_of_ne_zero hc
  have hsum : (event.card : ℝ) * center ^ 2 ≤
      ∑ ω : Ω, (X ω - center) ^ 2 := by
    calc
      (event.card : ℝ) * center ^ 2 = ∑ _ω ∈ event, center ^ 2 := by simp
      _ ≤ ∑ ω ∈ event, (X ω - center) ^ 2 := by
        apply Finset.sum_le_sum
        intro ω hω
        simp [hevent ω hω]
      _ ≤ ∑ ω : Ω, (X ω - center) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ event)
          (fun ω _ _ => sq_nonneg _)
  unfold uniformAverage
  apply (le_div_iff₀ hc2).mpr
  rw [div_mul_eq_mul_div]
  exact (div_le_div_iff_of_pos_right hcard).mpr hsum


end SatUpper
