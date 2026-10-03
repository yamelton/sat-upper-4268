import SatUpper.Ground.Comparison
import SatUpper.FiniteUniformLaw

/-! At the clause-only endpoint, ground entropy is exactly minus the mean energy. -/

open MeasureTheory SatUpper.DirectFinite SatUpper.GroundFinite

namespace SatUpper.GroundClause

instance (n : ℕ) [NeZero n] : IsProbabilityMeasure (ClauseEndpoint.clauseLaw n) := by
  unfold ClauseEndpoint.clauseLaw
  infer_instance

theorem forget_law (n : ℕ) [NeZero n] :
    Measure.map (fun x : Fresh n => fun j => (x j).1) (freshLaw n) = ClauseEndpoint.clauseLaw n := by
  unfold freshLaw
  rw [Measure.pi_map_pi (fun _ => measurable_fst.aemeasurable)]
  simp only [seedLaw, Measure.map_fst_prod, measure_univ, one_smul]
  simp_rw [DirectProduct.uniform_eq_count]
  rfl

theorem entropy_eq {n K : ℕ} (y : ℝ) (c : Fin K → Fresh n) :
    entropy y c Fin.elim0 = -y * energy c Fin.elim0 Fin.elim0 := by
  have he (a : Fields 0) : a = Fin.elim0 := Subsingleton.elim _ _
  simp only [GroundFinite.entropy, GroundFinite.moment, he, integral_const,
    measureReal_univ_eq_one, one_smul, Real.log_exp]

theorem energy_eq {n K : ℕ} (c : Fin K → Fresh n) :
    energy c Fin.elim0 Fin.elim0 = GroundFormula.energy (fun i j => (c i j).1) := by
  unfold energy GroundFormula.energy
  congr 1

theorem fixed_mean {n K : ℕ} [NeZero n] (y : ℝ) :
    GroundComparison.mean n y K 0 = -y * GroundFormula.mean n K := by
  have hp := Measure.pi_map_pi (μ := fun _ : Fin K => freshLaw n)
    (f := fun _ => fun x : Fresh n => fun j => (x j).1)
    (fun _ => (measurable_of_countable _).aemeasurable)
  simp only [forget_law n] at hp
  unfold GroundFormula.mean
  rw [← FiniteUniformLaw.clause_family_integral n K, ← hp,
    integral_map (measurable_of_countable _).aemeasurable (measurable_of_countable _).aestronglyMeasurable]
  have he (s : Fin 0 → Fresh n) : s = Fin.elim0 := Subsingleton.elim _ _
  simp only [GroundComparison.mean, he, integral_const, measureReal_univ_eq_one, one_smul,
    entropy_eq, energy_eq, integral_const_mul]

end SatUpper.GroundClause
