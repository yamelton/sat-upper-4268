import SatUpper.Ground.Insertion
import SatUpper.Direct.Poisson

/-! Average the finite insertion inequality, then compare the two Poisson endpoints.

This specializes the clause/site Poisson interpolation of Franz–Leone,
Section III.B (51)–(54), https://arxiv.org/pdf/cond-mat/0208280, to integer
minimum costs. `GroundFinite.fractional_entropy_bounds` relates the functional
used here to a nested partition moment for the same finite field law.
-/

open MeasureTheory SatUpper.DirectFinite SatUpper.GroundFinite SatUpper.GroundInsertion
open scoped NNReal

namespace SatUpper.GroundComparison

noncomputable def mean (n : ℕ) [NeZero n] (y : ℝ) (K L : ℕ) : ℝ :=
  ∫ c : Fin K → Fresh n, ∫ s : Fin L → Fresh n, entropy y c s
    ∂Measure.pi (fun _ => freshLaw n) ∂Measure.pi (fun _ => freshLaw n)

variable {n : ℕ} [NeZero n]

theorem clause_difference (y : ℝ) (K L : ℕ) :
    mean n y (K+1) L-mean n y K L =
      ∫ c : Fin K → Fresh n, ∫ s : Fin L → Fresh n,
        ∫ x, entropy y (Fin.cons x c) s-entropy y c s ∂freshLaw n
        ∂Measure.pi (fun _ => freshLaw n) ∂Measure.pi (fun _ => freshLaw n) := by
  have he (c : Fin K → Fresh n) :
      (∫ x, ∫ s : Fin L → Fresh n, entropy y (Fin.cons x c) s
        ∂Measure.pi (fun _ => freshLaw n) ∂freshLaw n) =
      ∫ s : Fin L → Fresh n, ∫ x, entropy y (Fin.cons x c) s
        ∂freshLaw n ∂Measure.pi (fun _ => freshLaw n) := integral_integral_swap Integrable.of_finite
  unfold mean
  rw [DirectProduct.integral_iid_cons]
  simp_rw [he, integral_sub Integrable.of_finite Integrable.of_finite,
    integral_const, measureReal_univ_eq_one, one_smul]

theorem site_difference (y : ℝ) (K L : ℕ) :
    mean n y K (L+1)-mean n y K L =
      ∫ c : Fin K → Fresh n, ∫ s : Fin L → Fresh n,
        ∫ x, entropy y c (Fin.cons x s)-entropy y c s ∂freshLaw n
        ∂Measure.pi (fun _ => freshLaw n) ∂Measure.pi (fun _ => freshLaw n) := by
  unfold mean
  simp_rw [DirectProduct.integral_iid_cons,
    integral_sub Integrable.of_finite Integrable.of_finite,
    integral_const, measureReal_univ_eq_one, one_smul]

theorem clause_difference_bound {y : ℝ} (hy : 0 ≤ y) (K L : ℕ) :
    ‖mean n y (K+1) L-mean n y K L‖ ≤ y := by
  rw [clause_difference]
  have h1 (c : Fin K → Fresh n) (s : Fin L → Fresh n) :
      ‖∫ x, entropy y (Fin.cons x c) s-entropy y c s ∂freshLaw n‖ ≤ y := by
    simpa using norm_integral_le_of_norm_le_const (μ := freshLaw n)
      (Filter.Eventually.of_forall (clause_increment_bound hy c s))
  have h2 (c : Fin K → Fresh n) :
      ‖∫ s : Fin L → Fresh n, ∫ x, entropy y (Fin.cons x c) s-entropy y c s
        ∂freshLaw n ∂Measure.pi (fun _ => freshLaw n)‖ ≤ y := by
    simpa using norm_integral_le_of_norm_le_const (μ := Measure.pi (fun _ : Fin L => freshLaw n))
      (Filter.Eventually.of_forall (h1 c))
  simpa using norm_integral_le_of_norm_le_const (μ := Measure.pi (fun _ : Fin K => freshLaw n))
    (Filter.Eventually.of_forall h2)

theorem site_difference_bound {y : ℝ} (hy : 0 ≤ y) (K L : ℕ) :
    ‖mean n y K (L+1)-mean n y K L‖ ≤ y := by
  rw [site_difference]
  have h1 (c : Fin K → Fresh n) (s : Fin L → Fresh n) :
      ‖∫ x, entropy y c (Fin.cons x s)-entropy y c s ∂freshLaw n‖ ≤ y := by
    simpa using norm_integral_le_of_norm_le_const (μ := freshLaw n)
      (Filter.Eventually.of_forall (site_increment_bound hy c s))
  have h2 (c : Fin K → Fresh n) :
      ‖∫ s : Fin L → Fresh n, ∫ x, entropy y c (Fin.cons x s)-entropy y c s
        ∂freshLaw n ∂Measure.pi (fun _ => freshLaw n)‖ ≤ y := by
    simpa using norm_integral_le_of_norm_le_const (μ := Measure.pi (fun _ : Fin L => freshLaw n))
      (Filter.Eventually.of_forall (h1 c))
  simpa using norm_integral_le_of_norm_le_const (μ := Measure.pi (fun _ : Fin K => freshLaw n))
    (Filter.Eventually.of_forall h2)

theorem difference_sign {y : ℝ} (hy : 0 ≤ y) (K L : ℕ) :
    mean n y (K+1) L-mean n y K L - 3*(mean n y K (L+1)-mean n y K L) +
      2*edgeMean n y ≤ 0 := by
  have hi (c : Fin K → Fresh n) := integral_nonpos (μ := Measure.pi (fun _ : Fin L => freshLaw n))
    (fun s => cubic_nonpos hy c s)
  have h := integral_nonpos (μ := Measure.pi (fun _ : Fin K => freshLaw n)) hi
  rw [clause_difference y K L, site_difference y K L]
  simpa only [integral_add Integrable.of_finite Integrable.of_finite,
    integral_sub Integrable.of_finite Integrable.of_finite, integral_const_mul,
    integral_const, measureReal_univ_eq_one, one_smul] using h

theorem endpoint_comparison {y : ℝ} (hy : 0 ≤ y)
    (a : ℝ≥0) :
    DirectPoisson.expectation (mean n y) a 0 ≤
      DirectPoisson.expectation (mean n y) 0 (3*a) -
        2*a*edgeMean n y :=
  DirectPoisson.comparison (clause_difference_bound hy)
    (site_difference_bound hy) (difference_sign hy) a

end SatUpper.GroundComparison
