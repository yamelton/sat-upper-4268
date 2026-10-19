import SatKUpper.BetaCertificate
import SatUpper.Enclosures

/-! Rational interval certificates for the beta recurrence and tilted
moments. The tables are checked by finite inequalities, not trusted. -/

namespace SatKUpper.BetaEnclosures

def ratio (a b : ℚ) (h : ℕ) : ℚ := (a+h)/(a+b+h)

def normalizer (a b τ : ℚ) : ℚ := 1+τ*a*b/((a+b)*(a+b+1))

def multiplier (a b τ : ℚ) (h : ℕ) : ℚ := normalizer (a+h) b τ / normalizer a b τ

theorem normalizer_cast (a b τ : ℚ) :
    (normalizer a b τ : ℝ) = TiltedBeta.Z a b τ := by
  simp [normalizer, TiltedBeta.Z]

theorem multiplier_nonneg {a b τ : ℚ} (ha : 0 < a) (hb : 0 < b) (ht : -4 ≤ τ) (h : ℕ) :
    0 ≤ multiplier a b τ h := by
  have h0 := TiltedBeta.Z_pos (by exact_mod_cast ha : (0 : ℝ) < a)
    (by exact_mod_cast hb : (0 : ℝ) < b) (by exact_mod_cast ht : (-4 : ℝ) ≤ τ)
  have h1 := TiltedBeta.Z_pos (by positivity : (0 : ℝ) < (a : ℝ)+h)
    (by exact_mod_cast hb : (0 : ℝ) < b) (by exact_mod_cast ht : (-4 : ℝ) ≤ τ)
  have h0' : 0 < normalizer a b τ := by rw [← normalizer_cast] at h0; exact_mod_cast h0
  have h1' : 0 < normalizer (a+h) b τ := by
    have he : (normalizer (a+h) b τ : ℝ) = TiltedBeta.Z ((a : ℝ)+h) b τ := by
      rw [normalizer_cast]; push_cast; rfl
    rw [← he] at h1
    exact_mod_cast h1
  exact (div_pos h1' h0').le

theorem moment_eq (a b τ : ℚ) (h : ℕ) :
    TiltedBeta.m a b τ h = BetaMoments.u a b h * (multiplier a b τ h : ℝ) := by
  unfold TiltedBeta.m multiplier
  simp only [Rat.cast_div, normalizer_cast, Rat.cast_add, Rat.cast_natCast]
  unfold TiltedBeta.Z
  ring_nf

theorem recurrence_bounds {a b : ℚ} (ha : 0 < a) (hb : 0 < b)
    (l u : ℕ → ℚ) (N : ℕ) (h0 : l 0 ≤ 1 ∧ 1 ≤ u 0)
    (hstep : ∀ h, h < N → l (h+1) ≤ l h * ratio a b h ∧ u h * ratio a b h ≤ u (h+1)) :
    ∀ h, h ≤ N → (l h : ℝ) ≤ BetaMoments.u a b h ∧ BetaMoments.u a b h ≤ (u h : ℝ) := by
  intro h hh
  induction h with
  | zero => simpa only [BetaMoments.u_zero] using
      (show (l 0 : ℝ) ≤ 1 ∧ 1 ≤ (u 0 : ℝ) by exact_mod_cast h0)
  | succ h ih =>
    have hi := ih (by omega)
    have hc := hstep h (by omega)
    have hr : (0 : ℝ) ≤ (ratio a b h : ℚ) := by
      have haR : (0 : ℝ) < a := by exact_mod_cast ha
      have hbR : (0 : ℝ) < b := by exact_mod_cast hb
      simp only [ratio, Rat.cast_div, Rat.cast_add, Rat.cast_natCast]
      positivity
    have he : ((ratio a b h : ℚ) : ℝ) = ((a : ℝ)+h)/((a : ℝ)+b+h) := by simp [ratio]
    rw [BetaMoments.u_succ, ← he]
    constructor
    · exact (show (l (h+1) : ℝ) ≤ (l h : ℝ)*(ratio a b h : ℚ) by exact_mod_cast hc.1).trans
        (mul_le_mul_of_nonneg_right hi.1 hr)
    · exact (mul_le_mul_of_nonneg_right hi.2 hr).trans
        (show (u h : ℝ)*(ratio a b h : ℚ) ≤ (u (h+1) : ℝ) by exact_mod_cast hc.2)

theorem moment_bounds {a b τ : ℚ} (ha : 0 < a) (hb : 0 < b) (ht : -4 ≤ τ)
    {h : ℕ} {l u ml mu : ℚ}
    (hl : (l : ℝ) ≤ BetaMoments.u a b h) (hu : BetaMoments.u a b h ≤ (u : ℝ))
    (hml : ml ≤ l*multiplier a b τ h) (hmu : u*multiplier a b τ h ≤ mu) :
    (ml : ℝ) ≤ TiltedBeta.m a b τ h ∧ TiltedBeta.m a b τ h ≤ (mu : ℝ) := by
  have hm : (0 : ℝ) ≤ (multiplier a b τ h : ℚ) := by exact_mod_cast multiplier_nonneg ha hb ht h
  rw [moment_eq]
  constructor
  · exact (show (ml : ℝ) ≤ (l : ℝ)*(multiplier a b τ h : ℚ) by exact_mod_cast hml).trans
      (mul_le_mul_of_nonneg_right hl hm)
  · exact (mul_le_mul_of_nonneg_right hu hm).trans
      (show (u : ℝ)*(multiplier a b τ h : ℚ) ≤ (mu : ℝ) by exact_mod_cast hmu)

theorem power_bounds {l u pl pu : ℚ} {x : ℝ} (hx : 0 ≤ x) (hl0 : 0 ≤ l)
    (hl : (l : ℝ) ≤ x) (hu : x ≤ (u : ℝ)) (k : ℕ)
    (hpl : pl ≤ l^k) (hpu : u^k ≤ pu) : (pl : ℝ) ≤ x^k ∧ x^k ≤ (pu : ℝ) := by
  constructor
  · exact (show (pl : ℝ) ≤ (l : ℝ)^k by exact_mod_cast hpl).trans
      (pow_le_pow_left₀ (by exact_mod_cast hl0) hl k)
  · exact (pow_le_pow_left₀ hx hu k).trans
      (show (u : ℝ)^k ≤ (pu : ℝ) by exact_mod_cast hpu)

end SatKUpper.BetaEnclosures
