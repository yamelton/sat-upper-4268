import SatUpper.PoissonExpectation
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! A finite binomial replacement proves the Poisson clause/site comparison.
The coefficients 1, 2, and 3 are the same balance as in the interpolation
argument; the Cauchy product performs the Poisson averaging without calculus. -/

namespace SatUpper.BinomialPoisson

open Finset MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Unnormalized binomial mixture of clause insertions and empty slots. -/
noncomputable def mixture (f : ℕ → ℕ → ℝ) (n K L : ℕ) : ℝ :=
  ∑ k ∈ range (n+1), (n.choose k : ℝ)*2^(n-k)*f (K+k) L

theorem mixture_zero (f : ℕ → ℕ → ℝ) (K L : ℕ) : mixture f 0 K L = f K L := by
  simp [mixture]

theorem mixture_succ (f : ℕ → ℕ → ℝ) (n K L : ℕ) :
    mixture f (n+1) K L = mixture f n (K+1) L + 2*mixture f n K L := by
  unfold mixture
  have h := Finset.sum_choose_succ_mul (fun k l => (2 : ℝ)^l*f (K+k) L) n
  simp only [mul_assoc] at *
  rw [h, add_comm]
  simp only [Finset.mul_sum]
  congr 1
  · apply sum_congr rfl
    intro k hk
    simp only [Nat.add_assoc, Nat.add_comm 1 k]
  · apply sum_congr rfl
    intro k hk
    have hk : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have he : n+1-k = n-k+1 := by omega
    rw [he, pow_succ]
    ring

theorem mixture_le {f : ℕ → ℕ → ℝ} {d : ℝ}
    (h : ∀ K L, f (K+1) L - 3*f K (L+1) + 2*f K L + 2*d ≤ 0)
    (n K L : ℕ) : mixture f n K L ≤ 3^n*(f K (L+n) - 2*n*d/3) := by
  induction n generalizing K L with
  | zero => simp [mixture_zero]
  | succ n ih =>
    rw [mixture_succ]
    have h₁ := ih (K+1) L
    have h₂ := mul_le_mul_of_nonneg_left (ih K L) (by norm_num : (0 : ℝ) ≤ 2)
    have h₃ := mul_le_mul_of_nonneg_left (h K (L+n)) (by positivity : (0 : ℝ) ≤ 3^n)
    push_cast
    rw [pow_succ]
    have he : L+(n+1) = L+n+1 := by omega
    rw [he]
    nlinarith

theorem mixture_series {f : ℕ → ℕ → ℝ} {A B : ℝ}
    (hg : ∀ n, ‖f n 0‖ ≤ A+B*n) (a : ℝ) :
    HasSum (fun n => mixture f n 0 0 * a^n / (n.factorial : ℝ))
      ((∑' n, f n 0 * a^n / (n.factorial : ℝ))*Real.exp (2*a)) := by
  have hf : Summable (fun n => ‖f n 0 * a^n / (n.factorial : ℝ)‖) := by
    simpa only [norm_div, norm_mul, norm_pow, Real.norm_eq_abs a, Real.norm_natCast] using
      PoissonExpectation.summable_exp_series_of_linear_growth
        (f := fun n => ‖f n 0‖) (by simpa only [norm_norm] using hg) |a|
  have hg' : Summable (fun n => ‖(2*a)^n / (n.factorial : ℝ)‖) := by
    simpa only [norm_div, norm_pow, Real.norm_eq_abs (2*a), Real.norm_natCast] using
      (NormedSpace.expSeries_div_hasSum_exp ℝ |2*a|).summable
  have he := NormedSpace.expSeries_div_hasSum_exp ℝ (2*a)
  have hc := hasSum_sum_range_mul_of_summable_norm
    hf hg'
  rw [he.tsum_eq, ← Real.exp_eq_exp_ℝ] at hc
  convert hc using 1
  funext n
  unfold mixture
  simp only [zero_add, Finset.sum_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  have hk : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hp : a^n = a^k*a^(n-k) := by rw [← pow_add, Nat.add_sub_of_le hk]
  have hfac (n : ℕ) : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [Nat.cast_choose ℝ hk, mul_pow, hp]
  field_simp

/-- A finite binomial replacement followed by a Poisson average.
The Poisson Cauchy product absorbs the empty slots. No differentiation is used. -/
theorem comparison {f : ℕ → ℕ → ℝ} {C d : ℝ}
    (hC : ∀ K L, ‖f (K+1) L-f K L‖ ≤ C)
    (hS : ∀ K L, ‖f K (L+1)-f K L‖ ≤ C)
    (h : ∀ K L, f (K+1) L - 3*f K (L+1) + 2*f K L + 2*d ≤ 0)
    (a : ℝ≥0) :
    PoissonExpectation.poissonExpectation (fun K => f K 0) a ≤
      PoissonExpectation.poissonExpectation (f 0) (3*a) - 2*a*d := by
  have hgC := PoissonExpectation.linear_growth_of_bounded_increments (f := fun K => f K 0) (fun K => hC K 0)
  have hgS := PoissonExpectation.linear_growth_of_bounded_increments (hS 0)
  have hl := (mixture_series hgC (a : ℝ)).mul_left (Real.exp (-3*(a : ℝ)))
  have hr := ((PoissonExpectation.summable_exp_series_of_linear_growth hgS (3*a)).hasSum).mul_left
    (Real.exp (-3*(a : ℝ)))
  have hm := (Campbell.poisson_mean_series (3*a)).mul_left (2*d/3)
  have hb := hasSum_le (fun n => ?_) hl (hr.sub hm)
  · have he : Real.exp (-3*(a : ℝ))*Real.exp (2*a) = Real.exp (-(a : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    convert hb using 1
    · unfold PoissonExpectation.poissonExpectation
      rw [← he]
      ring
    · simp only [NNReal.coe_mul, NNReal.coe_ofNat]
      unfold PoissonExpectation.poissonExpectation
      simp only [neg_mul]
      ring
  · have hh := mul_le_mul_of_nonneg_left (mixture_le h n 0 0)
      (by positivity : 0 ≤ Real.exp (-3*(a : ℝ)) * (a : ℝ)^n / (n.factorial : ℝ))
    convert hh using 1
    · ring
    · simp only [zero_add, poissonPMFReal, NNReal.coe_mul, NNReal.coe_ofNat, mul_pow, neg_mul]
      ring

end SatUpper.BinomialPoisson
