import SatUpper.PoissonExpectation
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul

/-! First and second moments of the clause-count Poisson distribution. -/

open MeasureTheory ProbabilityTheory SatUpper.PoissonExpectation
open scoped NNReal ENNReal

namespace SatUpper.PoissonCountMoments

theorem second_series (r : ℝ≥0) :
    HasSum (fun n => poissonPMFReal r n * (n : ℝ)^2) ((r : ℝ)^2+r) := by
  apply (hasSum_nat_add_iff' 1).mp
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_pow (by decide : 2 ≠ 0),
    mul_zero, sub_zero, Nat.cast_add, Nat.cast_one]
  have he (n : ℕ) : poissonPMFReal r (n+1) * ((n : ℝ)+1)^2 =
      (r : ℝ) * (poissonPMFReal r n * (n : ℝ)) + (r : ℝ) * poissonPMFReal r n := by
    have h := Campbell.poisson_weight_succ r n
    nlinarith
  simp_rw [he]
  convert ((Campbell.poisson_mean_series r).mul_left (r : ℝ)).add
    ((poissonPMFRealSum r).mul_left (r : ℝ)) using 1
  ring

theorem integrable_count (r : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ)) (poissonMeasure r) := by
  apply integrable_of_weighted r
  simpa using (Campbell.poisson_mean_series r).summable

theorem integrable_square (r : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ)^2) (poissonMeasure r) := by
  apply integrable_of_weighted r
  simpa using (second_series r).summable

theorem integral_count (r : ℝ≥0) :
    (∫ n : ℕ, (n : ℝ) ∂poissonMeasure r) = r := by
  rw [integral_eq_series r (integrable_count r)]
  exact (Campbell.poisson_mean_series r).tsum_eq

theorem integral_square (r : ℝ≥0) :
    (∫ n : ℕ, (n : ℝ)^2 ∂poissonMeasure r) = (r : ℝ)^2+r := by
  rw [integral_eq_series r (integrable_square r)]
  exact (second_series r).tsum_eq

theorem integrable_centered_square (r : ℝ≥0) (a : ℝ) :
    Integrable (fun n : ℕ => ((n : ℝ)-a)^2) (poissonMeasure r) := by
  have h := ((integrable_square r).sub ((integrable_count r).const_mul (2*a))).add
    (integrable_const (a^2))
  convert h using 1
  funext n
  dsimp only [Pi.add_apply, Pi.sub_apply]
  ring

theorem integral_centered_square (r : ℝ≥0) (a : ℝ) :
    (∫ n : ℕ, ((n : ℝ)-a)^2 ∂poissonMeasure r) = (r : ℝ) + ((r : ℝ)-a)^2 := by
  have he (n : ℕ) : ((n : ℝ)-a)^2 = (n : ℝ)^2 - 2*a*(n : ℝ) + a^2 := by ring
  simp_rw [he]
  have hi : Integrable (fun n : ℕ => (n : ℝ)^2 - 2*a*(n : ℝ)) (poissonMeasure r) :=
    (integrable_square r).sub ((integrable_count r).const_mul (2*a))
  rw [integral_add hi (integrable_const _),
    integral_sub (integrable_square r) ((integrable_count r).const_mul (2*a)),
    integral_const_mul, integral_count, integral_square, integral_const]
  simp only [measureReal_univ_eq_one, one_smul]
  ring

/-- Jensen's inequality for the square bounds the mean absolute count error. -/
theorem integral_abs_le_sqrt (r : ℝ≥0) (a : ℝ) (ha : |(r : ℝ)-a| ≤ 1) :
    (∫ n : ℕ, |(n : ℝ)-a| ∂poissonMeasure r) ≤ Real.sqrt ((r : ℝ)+1) := by
  have hi := ((integrable_count r).sub (integrable_const a)).abs
  have hj : Integrable (fun n : ℕ => |(n : ℝ)-a| ^ 2) (poissonMeasure r) := by
    simpa only [sq_abs] using integrable_centered_square r a
  have h := (convexOn_pow (𝕜 := ℝ) 2).map_integral_le (by fun_prop) isClosed_Ici
    (Filter.Eventually.of_forall fun n : ℕ => abs_nonneg ((n : ℝ)-a)) hi hj
  simp only [sq_abs, integral_centered_square] at h
  apply Real.le_sqrt_of_sq_le
  exact h.trans (add_le_add_left ((sq_le_one_iff_abs_le_one _).mpr ha) _)

theorem integral_abs_floor_le (r : ℝ≥0) :
    (∫ n : ℕ, |(⌊(r : ℝ)⌋₊ : ℝ)-(n : ℝ)| ∂poissonMeasure r) ≤ Real.sqrt ((r : ℝ)+1) := by
  have hf := Nat.floor_le r.coe_nonneg
  have hg := Nat.lt_floor_add_one (r : ℝ)
  have ha : |(r : ℝ)-(⌊(r : ℝ)⌋₊ : ℝ)| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hf)]
    linarith
  simpa only [abs_sub_comm] using integral_abs_le_sqrt r (⌊(r : ℝ)⌋₊ : ℝ) ha

/-- Bounded discrete increments control the cost of fixing the Poisson count. -/
theorem fixed_floor_le {f : ℕ → ℝ} {C : ℝ}
    (hC : ∀ K, ‖f (K+1)-f K‖ ≤ C) (r : ℝ≥0) :
    f ⌊(r : ℝ)⌋₊ ≤ (∫ K, f K ∂poissonMeasure r) + C*Real.sqrt ((r : ℝ)+1) := by
  have h0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hd (K H : ℕ) : |f K-f H| ≤ C*|(K : ℝ)-H| := by
    wlog h : K ≤ H generalizing K H
    · simpa only [abs_sub_comm] using this H K (le_of_not_ge h)
    have hs := dist_le_Ico_sum_of_dist_le (f := f) (d := fun _ => C) h
      (fun {j} _ _ => by simpa only [dist_eq_norm, norm_sub_rev] using hC j)
    simpa [Real.dist_eq, Nat.cast_sub h,
      abs_of_nonpos (sub_nonpos.mpr (Nat.cast_le.mpr h)), mul_comm] using hs
  have hi := integrable_poisson_of_linear_growth (linear_growth_of_bounded_increments hC) r
  have he := ((integrable_const (⌊(r : ℝ)⌋₊ : ℝ)).sub (integrable_count r)).abs
  have h := integral_mono (integrable_const (f ⌊(r : ℝ)⌋₊)) (hi.add (he.const_mul C))
    (fun K => by have := (le_abs_self _).trans (hd ⌊(r : ℝ)⌋₊ K); dsimp; linarith)
  simp only [Pi.add_apply, integral_add hi (he.const_mul C), integral_const_mul,
    integral_const, measureReal_univ_eq_one, one_smul] at h
  exact h.trans (add_le_add_left (mul_le_mul_of_nonneg_left (integral_abs_floor_le r) h0) _)

end SatUpper.PoissonCountMoments
