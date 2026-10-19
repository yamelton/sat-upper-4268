import SatKUpper.LocalComparison
import SatKUpper.PoissonComparison

/-! Average the general clause/site insertion and compare its Poisson endpoints. -/

open MeasureTheory SatKUpper.Sampling SatKUpper.Ground SatKUpper.LocalComparison SatUpper
open scoped NNReal

namespace SatKUpper.MeanComparison

noncomputable def mean {t : ℕ} (law : CoinLaw t) (r n : ℕ) [NeZero n] (y : ℝ) (K L : ℕ) : ℝ :=
  ∫ c : Fin K → Fresh t r n, ∫ s : Fin L → Fresh t r n, entropy law y c s
    ∂Measure.pi (fun _ => freshLaw law r n) ∂Measure.pi (fun _ => freshLaw law r n)

variable {t r n : ℕ} [NeZero n] (law : CoinLaw t)

theorem clause_difference (y : ℝ) (K L : ℕ) :
    mean law r n y (K+1) L-mean law r n y K L =
      ∫ c : Fin K → Fresh t r n, ∫ s : Fin L → Fresh t r n,
        ∫ x, entropy law y (Fin.cons x c) s-entropy law y c s ∂freshLaw law r n
        ∂Measure.pi (fun _ => freshLaw law r n) ∂Measure.pi (fun _ => freshLaw law r n) := by
  have he (c : Fin K → Fresh t r n) :
      (∫ x, ∫ s : Fin L → Fresh t r n, entropy law y (Fin.cons x c) s
        ∂Measure.pi (fun _ => freshLaw law r n) ∂freshLaw law r n) =
      ∫ s : Fin L → Fresh t r n, ∫ x, entropy law y (Fin.cons x c) s
        ∂freshLaw law r n ∂Measure.pi (fun _ => freshLaw law r n) := integral_integral_swap Integrable.of_finite
  unfold mean
  rw [DirectProduct.integral_iid_cons]
  simp_rw [he, integral_sub Integrable.of_finite Integrable.of_finite,
    integral_const, measureReal_univ_eq_one, one_smul]

theorem site_difference (y : ℝ) (K L : ℕ) :
    mean law r n y K (L+1)-mean law r n y K L =
      ∫ c : Fin K → Fresh t r n, ∫ s : Fin L → Fresh t r n,
        ∫ x, entropy law y c (Fin.cons x s)-entropy law y c s ∂freshLaw law r n
        ∂Measure.pi (fun _ => freshLaw law r n) ∂Measure.pi (fun _ => freshLaw law r n) := by
  unfold mean
  simp_rw [DirectProduct.integral_iid_cons,
    integral_sub Integrable.of_finite Integrable.of_finite,
    integral_const, measureReal_univ_eq_one, one_smul]

theorem clause_difference_bound {y : ℝ} (hy : 0 ≤ y) (K L : ℕ) :
    ‖mean law r n y (K+1) L-mean law r n y K L‖ ≤ y := by
  rw [clause_difference law]
  have h1 (c : Fin K → Fresh t r n) (s : Fin L → Fresh t r n) :
      ‖∫ x, entropy law y (Fin.cons x c) s-entropy law y c s ∂freshLaw law r n‖ ≤ y := by
    simpa using norm_integral_le_of_norm_le_const (μ := freshLaw law r n)
      (Filter.Eventually.of_forall (clause_increment_bound law hy c s))
  have h2 (c : Fin K → Fresh t r n) :
      ‖∫ s : Fin L → Fresh t r n, ∫ x, entropy law y (Fin.cons x c) s-entropy law y c s
        ∂freshLaw law r n ∂Measure.pi (fun _ => freshLaw law r n)‖ ≤ y := by
    simpa using norm_integral_le_of_norm_le_const (μ := Measure.pi (fun _ : Fin L => freshLaw law r n))
      (Filter.Eventually.of_forall (h1 c))
  simpa using norm_integral_le_of_norm_le_const (μ := Measure.pi (fun _ : Fin K => freshLaw law r n))
    (Filter.Eventually.of_forall h2)

theorem site_difference_bound {y : ℝ} (hy : 0 ≤ y) (K L : ℕ) :
    ‖mean law r n y K (L+1)-mean law r n y K L‖ ≤ y := by
  rw [site_difference law]
  have h1 (c : Fin K → Fresh t r n) (s : Fin L → Fresh t r n) :
      ‖∫ x, entropy law y c (Fin.cons x s)-entropy law y c s ∂freshLaw law r n‖ ≤ y := by
    simpa using norm_integral_le_of_norm_le_const (μ := freshLaw law r n)
      (Filter.Eventually.of_forall (site_increment_bound law hy c s))
  have h2 (c : Fin K → Fresh t r n) :
      ‖∫ s : Fin L → Fresh t r n, ∫ x, entropy law y c (Fin.cons x s)-entropy law y c s
        ∂freshLaw law r n ∂Measure.pi (fun _ => freshLaw law r n)‖ ≤ y := by
    simpa using norm_integral_le_of_norm_le_const (μ := Measure.pi (fun _ : Fin L => freshLaw law r n))
      (Filter.Eventually.of_forall (h1 c))
  simpa using norm_integral_le_of_norm_le_const (μ := Measure.pi (fun _ : Fin K => freshLaw law r n))
    (Filter.Eventually.of_forall h2)

theorem difference_sign {y : ℝ} (hy : 0 ≤ y) (K L : ℕ) :
    mean law r n y (K+1) L-mean law r n y K L - (r+1 : ℝ)*(mean law r n y K (L+1)-mean law r n y K L) +
      (r : ℝ)*edgeMean law r n y ≤ 0 := by
  have hi (c : Fin K → Fresh t r n) := integral_nonpos (μ := Measure.pi (fun _ : Fin L => freshLaw law r n))
    (fun s => power_nonpos law hy c s)
  have h := integral_nonpos (μ := Measure.pi (fun _ : Fin K => freshLaw law r n)) hi
  rw [clause_difference law y K L, site_difference law y K L]
  simpa only [integral_add Integrable.of_finite Integrable.of_finite,
    integral_sub Integrable.of_finite Integrable.of_finite, integral_const_mul,
    integral_const, measureReal_univ_eq_one, one_smul] using h

theorem endpoint_comparison {y : ℝ} (hy : 0 ≤ y)
    (a : ℝ≥0) :
    DirectPoisson.expectation (mean law r n y) a 0 ≤
      DirectPoisson.expectation (mean law r n y) 0 ((r+1)*a) -
        (r : ℝ)*a*edgeMean law r n y :=
  SatKUpper.PoissonComparison.comparison r (clause_difference_bound law hy)
    (site_difference_bound law hy) (difference_sign law hy) a

end SatKUpper.MeanComparison
