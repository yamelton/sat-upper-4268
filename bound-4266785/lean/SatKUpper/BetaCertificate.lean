import SatKUpper.TiltedBeta
import SatKUpper.TelescopingTail

/-! The finite analytic beta certificate implies unsatisfiability in the
standard random k-SAT model. Parameters and truncations remain arbitrary. -/

open SatKUpper.BetaMoments SatKUpper.TiltedBeta
open scoped NNReal

namespace SatKUpper.BetaCertificate

noncomputable def tail (a b τ : ℝ) (r N : ℕ) : ℝ :=
  u a b N^(r+1)/(Z a b τ^(r+1)*N) * (1+(a+b+N)/((r+1 : ℝ)*b))

theorem tail_bound {a b τ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hτ0 : -4 ≤ τ) (hτ1 : τ ≤ 0) (r N : ℕ) (hN : 0 < N) :
    Summable (fun i : ℕ => m a b τ (N+i)^(r+1)/(N+i : ℕ)) ∧
      (∑' i : ℕ, m a b τ (N+i)^(r+1)/(N+i : ℕ)) ≤ tail a b τ r N := by
  have hz : 0 < Z a b τ := Z_pos ha hb hτ0
  have hzp : 0 < Z a b τ^(r+1) := pow_pos hz _
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hbase := TelescopingTail.beta_tail r ha hb (u_nonneg ha hb) (u_succ a b) N hN
  have hs := hbase.1.mul_left (1/Z a b τ^(r+1))
  have hdom (i : ℕ) : m a b τ (N+i)^(r+1)/(N+i : ℕ) ≤
      (1/Z a b τ^(r+1))*(u a b (N+i)^(r+1)/(N+i : ℕ)) := by
    calc
      _ ≤ (u a b (N+i)/Z a b τ)^(r+1)/(N+i : ℕ) :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (moment_nonneg ha hb hτ0 hτ1 _)
          (moment_le ha hb hτ0 hτ1 _) _) (Nat.cast_nonneg _)
      _ = _ := by rw [div_pow]; ring
  have hm := Summable.of_nonneg_of_le
    (fun i => div_nonneg (pow_nonneg (moment_nonneg ha hb hτ0 hτ1 _) _) (Nat.cast_nonneg _)) hdom hs
  refine ⟨hm, ?_⟩
  have hle := Summable.tsum_le_tsum hdom hm hs
  rw [tsum_mul_left] at hle
  have hle' := hle.trans (mul_le_mul_of_nonneg_left hbase.2 (by positivity))
  apply hle'.trans
  have he : tail a b τ r N - (1/Z a b τ^(r+1))*
      (((1+(a+b+(r : ℝ)*b)/N)/((r+1 : ℝ)*b))*u a b N^(r+1)) =
      u a b N^(r+1)/(Z a b τ^(r+1)*(r+1 : ℝ)*N) := by
    unfold tail
    field_simp
    ring
  have hp : 0 ≤ u a b N^(r+1)/(Z a b τ^(r+1)*(r+1 : ℝ)*N) :=
    div_nonneg (pow_nonneg (u_nonneg ha hb N) _) (by positivity)
  linarith

theorem correction_summable {a b τ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hτ0 : -4 ≤ τ) (hτ1 : τ ≤ 0) (r : ℕ) :
    Summable (fun h : ℕ => m a b τ (h+1)^(r+1)/(h+1 : ℝ)) := by
  simpa only [Nat.add_comm 1, Nat.cast_add, Nat.cast_one] using
    (tail_bound ha hb hτ0 hτ1 r 1 (by omega)).1

theorem correction_bound {a b τ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hτ0 : -4 ≤ τ) (hτ1 : τ ≤ 0) (r H : ℕ) :
    (∑' h : ℕ, m a b τ (h+1)^(r+1)/(h+1 : ℝ)) ≤
      (∑ h ∈ Finset.range H, m a b τ (h+1)^(r+1)/(h+1 : ℝ)) + tail a b τ r (H+1) := by
  have hs := correction_summable ha hb hτ0 hτ1 r
  rw [← hs.sum_add_tsum_nat_add H]
  apply add_le_add_left
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.cast_add, Nat.cast_one, add_assoc] using
    (tail_bound ha hb hτ0 hτ1 r (H+1) (by omega)).2

noncomputable def value (a b τ : ℝ) (r : ℕ) (α : ℝ) (T H : ℕ) : ℝ :=
  ContinuousCriterion.siteValue (m a b τ) r α T +
    (r : ℝ)*α*((∑ h ∈ Finset.range H, m a b τ (h+1)^(r+1)/(h+1 : ℝ)) + tail a b τ r (H+1))

theorem upperBound {a b τ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hτ0 : -4 ≤ τ) (hτ1 : τ ≤ 0) (r : ℕ) (α : ℝ≥0) (T H : ℕ)
    (hneg : value a b τ r α T H < 0) : Model.UpperBound (r+1) α := by
  letI := measure_probability ha hb hτ0 hτ1
  have he : ContinuousCriterion.moment (measure a b τ) = m a b τ := by
    funext h
    exact moment_identity ha hb hτ0 hτ1 h
  apply ContinuousCriterion.upperBound (measure a b τ) r T α
  · rw [he]
    exact correction_summable ha hb hτ0 hτ1 r
  · rw [he]
    apply lt_of_le_of_lt _ hneg
    unfold value
    exact add_le_add_left (mul_le_mul_of_nonneg_left (correction_bound ha hb hτ0 hτ1 r H)
      (by positivity : 0 ≤ (r : ℝ)*α)) _

end SatKUpper.BetaCertificate
