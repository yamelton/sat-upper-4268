import SatUpper.PoissonExpectation
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! A finite binomial replacement proves the Poisson clause/site comparison.
The nonnegative empty-slot weight is arbitrary; the Cauchy product performs the Poisson averaging without calculus. -/

namespace SatKUpper.BinomialPoisson

open SatUpper

open Finset MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Unnormalized binomial mixture of clause insertions and empty slots. -/
noncomputable def mixture (w : ℝ) (f : ℕ → ℕ → ℝ) (n K L : ℕ) : ℝ :=
  ∑ k ∈ range (n+1), (n.choose k : ℝ)*w^(n-k)*f (K+k) L

theorem mixture_zero (w : ℝ) (f : ℕ → ℕ → ℝ) (K L : ℕ) : mixture w f 0 K L = f K L := by
  simp [mixture]

theorem mixture_succ (w : ℝ) (f : ℕ → ℕ → ℝ) (n K L : ℕ) :
    mixture w f (n+1) K L = mixture w f n (K+1) L + w*mixture w f n K L := by
  unfold mixture
  have h := Finset.sum_choose_succ_mul (fun k l => w^l*f (K+k) L) n
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

theorem mixture_le {w : ℝ} (hw : 0 ≤ w) {f : ℕ → ℕ → ℝ} {d : ℝ}
    (h : ∀ K L, f (K+1) L - (w+1)*f K (L+1) + w*f K L + (w+1)*d ≤ 0)
    (n K L : ℕ) : mixture w f n K L ≤ (w+1)^n*(f K (L+n) - n*d) := by
  induction n generalizing K L with
  | zero => simp [mixture_zero]
  | succ n ih =>
    rw [mixture_succ]
    have h₁ := ih (K+1) L
    have h₂ := mul_le_mul_of_nonneg_left (ih K L) hw
    have h₃ := mul_le_mul_of_nonneg_left (h K (L+n)) (by positivity : (0 : ℝ) ≤ (w+1)^n)
    push_cast
    rw [pow_succ]
    have he : L+(n+1) = L+n+1 := by omega
    rw [he]
    nlinarith

theorem mixture_series (w : ℝ) {f : ℕ → ℕ → ℝ} {A B : ℝ}
    (hg : ∀ n, ‖f n 0‖ ≤ A+B*n) (a : ℝ) :
    HasSum (fun n => mixture w f n 0 0 * a^n / (n.factorial : ℝ))
      ((∑' n, f n 0 * a^n / (n.factorial : ℝ))*Real.exp (w*a)) := by
  have hf : Summable (fun n => ‖f n 0 * a^n / (n.factorial : ℝ)‖) := by
    simpa only [norm_div, norm_mul, norm_pow, Real.norm_eq_abs a, Real.norm_natCast] using
      PoissonExpectation.summable_exp_series_of_linear_growth
        (f := fun n => ‖f n 0‖) (by simpa only [norm_norm] using hg) |a|
  have hg' : Summable (fun n => ‖(w*a)^n / (n.factorial : ℝ)‖) := by
    simpa only [norm_div, norm_pow, Real.norm_eq_abs (w*a), Real.norm_natCast] using
      (NormedSpace.expSeries_div_hasSum_exp ℝ |w*a|).summable
  have he := NormedSpace.expSeries_div_hasSum_exp ℝ (w*a)
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
theorem comparison {w : ℝ} (hw : 0 ≤ w) {f : ℕ → ℕ → ℝ} {C d : ℝ}
    (hC : ∀ K L, ‖f (K+1) L-f K L‖ ≤ C)
    (hS : ∀ K L, ‖f K (L+1)-f K L‖ ≤ C)
    (h : ∀ K L, f (K+1) L - (w+1)*f K (L+1) + w*f K L + (w+1)*d ≤ 0)
    (a : ℝ≥0) :
    PoissonExpectation.poissonExpectation (fun K => f K 0) a ≤
      PoissonExpectation.poissonExpectation (f 0) ((w+1)*a) - (w+1)*a*d := by
  have hgC := PoissonExpectation.linear_growth_of_bounded_increments (f := fun K => f K 0) (fun K => hC K 0)
  have hgS := PoissonExpectation.linear_growth_of_bounded_increments (hS 0)
  have hl := (mixture_series w hgC (a : ℝ)).mul_left (Real.exp (-(w+1)*(a : ℝ)))
  have hr := ((PoissonExpectation.summable_exp_series_of_linear_growth hgS ((w+1)*a)).hasSum).mul_left
    (Real.exp (-(w+1)*(a : ℝ)))
  let rate : ℝ≥0 := ⟨(w+1)*(a : ℝ), by positivity⟩
  have hm := (Campbell.poisson_mean_series rate).mul_left d
  change HasSum (fun n => d * (poissonPMFReal rate n * (n : ℝ)))
    (d * ((w+1)*(a : ℝ))) at hm
  have hb := hasSum_le (fun n => ?_) hl (hr.sub hm)
  · have he : Real.exp (-(w+1)*(a : ℝ))*Real.exp (w*a) = Real.exp (-(a : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    convert hb using 1
    · unfold PoissonExpectation.poissonExpectation
      rw [← he]
      ring
    · unfold PoissonExpectation.poissonExpectation
      simp only [neg_mul]
      ring
  · have hh := mul_le_mul_of_nonneg_left (mixture_le hw h n 0 0)
      (by positivity : 0 ≤ Real.exp (-(w+1)*(a : ℝ)) * (a : ℝ)^n / (n.factorial : ℝ))
    convert hh using 1
    · ring
    · simp [poissonPMFReal, rate, mul_pow]
      ring

end SatKUpper.BinomialPoisson
