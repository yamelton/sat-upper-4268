import SatUpper.Local
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Order
import Mathlib.Tactic.Push

/-! Integer minima and the exact cost of inserting one constraint. -/

namespace SatUpper.GroundMinimum

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

noncomputable def value (H : Ω → ℕ) : ℕ := Finset.univ.inf' Finset.univ_nonempty H

theorem le_value {H : Ω → ℕ} {a : ℕ} (h : ∀ x, a ≤ H x) : a ≤ value H :=
  Finset.le_inf' _ _ (fun x _ => h x)

theorem value_le (H : Ω → ℕ) (x : Ω) : value H ≤ H x :=
  Finset.inf'_le H (Finset.mem_univ x)

theorem attained (H : Ω → ℕ) : ∃ x, H x = value H := by
  obtain ⟨x, _, hx⟩ := Finset.exists_mem_eq_inf' (s := Finset.univ) Finset.univ_nonempty H
  exact ⟨x, hx.symm⟩

theorem mono {H G : Ω → ℕ} (h : ∀ x, H x ≤ G x) : value H ≤ value G :=
  le_value (fun x => (value_le H x).trans (h x))

/-- A unit constraint costs one exactly when every minimizer violates it. -/
theorem insert (H : Ω → ℕ) (P : Ω → Prop) [DecidablePred P] :
    value (fun x => H x + if P x then 1 else 0) =
      value H + if ∀ x, H x = value H → P x then 1 else 0 := by
  classical
  by_cases h : ∀ x, H x = value H → P x
  · rw [if_pos h]
    apply le_antisymm
    · obtain ⟨x,hx⟩ := attained H
      exact (value_le _ x).trans_eq (by rw [hx, if_pos (h x hx)])
    · apply le_value
      intro x
      have hl := value_le H x
      by_cases hx : H x = value H
      · simp [hx, h x hx]
      · split <;> omega
  · rw [if_neg h, add_zero]
    push_neg at h
    obtain ⟨x,hx,hp⟩ := h
    exact le_antisymm ((value_le _ x).trans_eq (by simp [hx, hp]))
      (mono (fun _ => Nat.le_add_right _ _))

/-- The exponential insertion is an ordinary Bernoulli factor. -/
theorem exp_insert (H : Ω → ℕ) (P : Ω → Prop) [DecidablePred P] (y : ℝ) :
    Real.exp (-y * value (fun x => H x + if P x then 1 else 0)) =
      Real.exp (-y * value H) *
        (1-(1-Real.exp (-y)) * if ∀ x, H x = value H → P x then 1 else 0) := by
  classical
  rw [insert]
  split_ifs <;> simp [Nat.cast_add, mul_add, Real.exp_add]

/-- The finite-temperature log partition is within `log(card Ω)` of its minimum-energy term. -/
theorem log_partition_bounds (H : Ω → ℕ) {β : ℝ} (hβ : 0 ≤ β) :
    -β * value H ≤ Real.log (∑ x, Real.exp (-β * H x)) ∧
      Real.log (∑ x, Real.exp (-β * H x)) ≤ -β * value H + Real.log (Fintype.card Ω) := by
  classical
  obtain ⟨x,hx⟩ := attained H
  have hl : Real.exp (-β * value H) ≤ ∑ x, Real.exp (-β * H x) := by
    simpa [hx] using Finset.single_le_sum (fun x _ => (Real.exp_pos (-β * H x)).le)
      (Finset.mem_univ x)
  have hu : (∑ x, Real.exp (-β * H x)) ≤ Fintype.card Ω * Real.exp (-β * value H) := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
      Finset.sum_le_sum (s := Finset.univ) (fun x _ => Real.exp_le_exp.mpr
        (mul_le_mul_of_nonpos_left (Nat.cast_le.mpr (value_le H x)) (neg_nonpos.mpr hβ)))
  have hcard : (0 : ℝ) < Fintype.card Ω := Nat.cast_pos.mpr Fintype.card_pos
  refine ⟨by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hl, ?_⟩
  have h := Real.log_le_log ((Real.exp_pos _).trans_le hl) hu
  simpa only [Real.log_mul hcard.ne' (Real.exp_ne_zero _), Real.log_exp, add_comm] using h

end SatUpper.GroundMinimum
