import SatKUpper.Model
import SatKUpper.MeanComparison

/-! The clause endpoint is the actual uniform random formula, independent of the coin law. -/

open MeasureTheory SatKUpper.Sampling SatKUpper.Ground SatUpper
open scoped NNReal

namespace SatKUpper.ClauseEndpoint

theorem forget_law {t : ℕ} (law : CoinLaw t) (r n : ℕ) [NeZero n] :
    Measure.map (fun x : Fresh t r n => fun j => (x j).1) (freshLaw law r n) =
      Model.clauseLaw (r+1) n := by
  unfold freshLaw
  rw [Measure.pi_map_pi (fun _ => measurable_fst.aemeasurable)]
  simp only [seedLaw, Measure.map_fst_prod, measure_univ, one_smul]
  simp_rw [DirectProduct.uniform_eq_count]
  exact FiniteUniformLaw.pi_law (Fin n × Bool) (Fin (r+1))

theorem entropy_eq {t r n K : ℕ} (law : CoinLaw t) (y : ℝ) (c : Fin K → Fresh t r n) :
    entropy law y c Fin.elim0 = -y * energy c Fin.elim0 Fin.elim0 := by
  have he (a : Fields r 0) : a = Fin.elim0 := Subsingleton.elim _ _
  simp only [entropy, moment, he, integral_const,
    measureReal_univ_eq_one, one_smul, Real.log_exp]

theorem energy_eq {t r n K : ℕ} (c : Fin K → Fresh t r n) :
    energy c Fin.elim0 Fin.elim0 = Model.energy (fun i j => (c i j).1) := by
  unfold energy Model.energy
  congr 1

theorem fixed_mean {t r n K : ℕ} [NeZero n] (law : CoinLaw t) (y : ℝ) :
    MeanComparison.mean law r n y K 0 = -y * Model.mean (r+1) n K := by
  have hp := Measure.pi_map_pi (μ := fun _ : Fin K => freshLaw law r n)
    (f := fun _ => fun x : Fresh t r n => fun j => (x j).1)
    (fun _ => (measurable_of_countable _).aemeasurable)
  simp only [forget_law law r n] at hp
  unfold Model.mean
  rw [← Model.clause_family_integral (r+1) n K, ← hp,
    integral_map (measurable_of_countable _).aemeasurable (measurable_of_countable _).aestronglyMeasurable]
  have he (s : Fin 0 → Fresh t r n) : s = Fin.elim0 := Subsingleton.elim _ _
  simp only [MeanComparison.mean, he, integral_const, measureReal_univ_eq_one, one_smul,
    entropy_eq, energy_eq, integral_const_mul]

noncomputable def poissonMean (k n : ℕ) (a : ℝ≥0) : ℝ :=
  ∫ K, Model.mean k n K ∂ProbabilityTheory.poissonMeasure a

theorem poisson_mean_eq {t r n : ℕ} [NeZero n] (law : CoinLaw t) (y : ℝ) (a : ℝ≥0) :
    DirectPoisson.expectation (MeanComparison.mean law r n y) a 0 =
      -y*poissonMean (r+1) n a := by
  simp only [DirectPoisson.expectation, DirectPoisson.zero_law, integral_dirac,
    fixed_mean, integral_const_mul, poissonMean]

/-- The actual random-formula expected minimum is bounded by the site endpoint. -/
theorem energy_comparison {t r n : ℕ} [NeZero n] (law : CoinLaw t)
    {y : ℝ} (hy : 0 ≤ y) (a : ℝ≥0) :
    -y*poissonMean (r+1) n a ≤
      DirectPoisson.expectation (MeanComparison.mean law r n y) 0 ((r+1)*a) -
        (r : ℝ)*a*LocalComparison.edgeMean law r n y := by
  have h := MeanComparison.endpoint_comparison (r := r) (n := n) law hy a
  rwa [poisson_mean_eq] at h

end SatKUpper.ClauseEndpoint
