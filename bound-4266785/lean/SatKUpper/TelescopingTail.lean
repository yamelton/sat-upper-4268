import SatKUpper.PowerComparison
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Discrete tail estimates: no real powers or improper integrals are needed. -/

namespace SatKUpper.TelescopingTail

theorem power_decrement (r : ℕ) {q : ℝ} (hq : 0 ≤ q) :
    (r+1 : ℝ)*(1-q) ≤ (1-q^(r+1))*(1+(r : ℝ)*(1-q)) := by
  have h := PowerComparison.power_remainder_nonneg r (x := 1) (y := q) (by norm_num) hq
  simp only [one_pow] at h
  have hh := mul_nonneg hq h
  simp only [pow_succ] at *
  nlinarith

theorem beta_step (r : ℕ) {a b h u : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hh : 0 ≤ h) (hu : 0 ≤ u) :
    (r+1 : ℝ)*b*u^(r+1) ≤ (a+b+h+(r : ℝ)*b)*
      (u^(r+1)-(u*((a+h)/(a+b+h)))^(r+1)) := by
  let D := a+b+h
  let q := (a+h)/D
  have hD : 0 < D := by dsimp [D]; positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have h := power_decrement r hq
  have he : (1-q)*D = b := by
    dsimp [q, D]
    field_simp
    ring
  have h₁ : (r+1 : ℝ)*b ≤ (1-q^(r+1))*(D+(r : ℝ)*b) := by
    have hm := mul_le_mul_of_nonneg_right h hD.le
    have he₁ : (r+1 : ℝ)*(1-q)*D = (r+1 : ℝ)*b := by rw [mul_assoc, he]
    have he₂ : (1-q^(r+1))*(1+(r : ℝ)*(1-q))*D =
        (1-q^(r+1))*(D+(r : ℝ)*b) := by
      calc
        _ = (1-q^(r+1))*(D+(r : ℝ)*((1-q)*D)) := by ring
        _ = _ := by rw [he]
    simpa only [he₁, he₂] using hm
  have h₂ := mul_le_mul_of_nonneg_right h₁ (pow_nonneg hu (r+1))
  change _ ≤ (D+(r : ℝ)*b)*(u^(r+1)-(u*q)^(r+1))
  rw [mul_pow]
  nlinarith [h₂]

theorem partial_sum_le {f v : ℕ → ℝ} {C : ℝ}
    (hstep : ∀ i, f i ≤ C*(v i-v (i+1))) (m : ℕ) :
    ∑ i ∈ Finset.range m, f i ≤ C*(v 0-v m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    linarith [hstep m]

theorem tail_bound {f v : ℕ → ℝ} {C : ℝ} (hf : ∀ i, 0 ≤ f i)
    (hv : ∀ i, 0 ≤ v i) (hC : 0 ≤ C)
    (hstep : ∀ i, f i ≤ C*(v i-v (i+1))) :
    Summable f ∧ (∑' i, f i) ≤ C*v 0 := by
  have hs (m : ℕ) : ∑ i ∈ Finset.range m, f i ≤ C*v 0 := by
    have h := partial_sum_le hstep m
    nlinarith [mul_nonneg hC (hv m)]
  exact ⟨summable_of_sum_range_le hf hs, Real.tsum_le_of_sum_range_le hf hs⟩

theorem weighted_beta_step (r : ℕ) {a b h u : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hh : 0 < h) (hu : 0 ≤ u) :
    u^(r+1)/h ≤ ((1+(a+b+(r : ℝ)*b)/h)/((r+1 : ℝ)*b))*
      (u^(r+1)-(u*((a+h)/(a+b+h)))^(r+1)) := by
  have hk : 0 < (r+1 : ℝ)*b := by positivity
  have hstep := beta_step r ha hb hh.le hu
  calc
    _ = ((r+1 : ℝ)*b*u^(r+1))/((r+1 : ℝ)*b*h) := by field_simp
    _ ≤ ((a+b+h+(r : ℝ)*b)*(u^(r+1)-(u*((a+h)/(a+b+h)))^(r+1)))/
        ((r+1 : ℝ)*b*h) := div_le_div_of_nonneg_right hstep (mul_pos hk hh).le
    _ = _ := by field_simp; ring

/-- A sharper correction tail from the beta-moment recurrence alone. -/
theorem beta_tail (r : ℕ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {u : ℕ → ℝ} (hu : ∀ h, 0 ≤ u h)
    (hrec : ∀ h, u (h+1) = u h*((a+h)/(a+b+h))) (N : ℕ) (hN : 0 < N) :
    Summable (fun i : ℕ => u (N+i)^(r+1)/(N+i : ℕ)) ∧
      (∑' i : ℕ, u (N+i)^(r+1)/(N+i : ℕ)) ≤
        ((1+(a+b+(r : ℝ)*b)/N)/((r+1 : ℝ)*b))*u N^(r+1) := by
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hk : 0 < (r+1 : ℝ)*b := by positivity
  let C := (1+(a+b+(r : ℝ)*b)/N)/((r+1 : ℝ)*b)
  have hstep (i : ℕ) : u (N+i)^(r+1)/(N+i : ℕ) ≤
      C*(u (N+i)^(r+1)-u (N+(i+1))^(r+1)) := by
    have hh : (0 : ℝ) < (N+i : ℕ) := Nat.cast_pos.mpr (by omega)
    have hNH : (N : ℝ) ≤ (N+i : ℕ) := by exact_mod_cast Nat.le_add_right N i
    have hratio : 0 ≤ (a+(N+i : ℕ))/(a+b+(N+i : ℕ)) := by positivity
    have hratio1 : (a+(N+i : ℕ))/(a+b+(N+i : ℕ)) ≤ 1 := by
      apply (div_le_one (by positivity)).2
      linarith
    have hpow : (u (N+i)*((a+(N+i : ℕ))/(a+b+(N+i : ℕ))))^(r+1) ≤
        u (N+i)^(r+1) :=
      pow_le_pow_left₀ (mul_nonneg (hu _) hratio)
        (mul_le_of_le_one_right (hu _) hratio1) _
    have hcoef : (1+(a+b+(r : ℝ)*b)/(N+i : ℕ))/((r+1 : ℝ)*b) ≤ C := by
      apply div_le_div_of_nonneg_right _ hk.le
      apply add_le_add_left
      exact div_le_div_of_nonneg_left (by positivity) hNR hNH
    have hs := (weighted_beta_step r ha hb hh (hu (N+i))).trans
      (mul_le_mul_of_nonneg_right hcoef (sub_nonneg.mpr hpow))
    simpa only [Nat.add_assoc, ← hrec] using hs
  have h := tail_bound (f := fun i : ℕ => u (N+i)^(r+1)/(N+i : ℕ))
    (v := fun i : ℕ => u (N+i)^(r+1)) (C := C)
    (fun i => div_nonneg (pow_nonneg (hu _) _) (Nat.cast_nonneg _))
    (fun i => pow_nonneg (hu _) _) (by dsimp [C]; positivity) hstep
  simpa only [Nat.add_zero] using h

end SatKUpper.TelescopingTail
