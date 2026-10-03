import SatUpper.LogEnclosures
import SatUpper.Obligations
import Mathlib.Tactic.FinCases

/-! Uniform logarithm bounds: evaluate one formula, without a table of edge triples. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace SatUpper.NumericalLogs

def edgeLower (i j k : Fin 4) : ℚ :=
  LogEnclosures.logOneSubLower
    (Formalization.badMass i * Formalization.badMass j * Formalization.badMass k) 32

theorem edge_log_lower (i j k : Fin 4) :
    (edgeLower i j k : ℝ) ≤ Real.log
      (1 - (Formalization.badMass i : ℝ) * (Formalization.badMass j : ℝ) *
        (Formalization.badMass k : ℝ)) := by
  have h : 0 ≤ Formalization.badMass i * Formalization.badMass j * Formalization.badMass k ∧
      Formalization.badMass i * Formalization.badMass j * Formalization.badMass k < 1 := by
    fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num [Formalization.badMass]
  simpa only [edgeLower, Rat.cast_mul] using
    (LogEnclosures.log_one_sub_enclosure h.1 h.2 32).1

def edgeUpper : ℚ :=
  -2 * Witness.alpha * ((∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, edgeLower i j k) / 64)

theorem edgeCorrection_le : Formalization.edgeCorrection ≤ (edgeUpper : ℝ) := by
  have hs := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) =>
    Finset.sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset (Fin 4))) =>
      Finset.sum_le_sum fun k (_ : k ∈ (Finset.univ : Finset (Fin 4))) => edge_log_lower i j k
  have h := mul_le_mul_of_nonpos_left
    (div_le_div_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 64))
    (by norm_num [Witness.alpha] : -2 * (Witness.alpha : ℝ) ≤ 0)
  simpa only [Formalization.edgeCorrection, edgeUpper, Rat.cast_mul, Rat.cast_div,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_sum] using h

end SatUpper.NumericalLogs
