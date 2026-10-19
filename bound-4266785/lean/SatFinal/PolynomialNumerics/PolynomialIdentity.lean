import SatFinal.PolynomialNumerics.Coefficient0
import SatFinal.PolynomialNumerics.Coefficient1
import SatFinal.PolynomialNumerics.Coefficient2
import SatFinal.PolynomialNumerics.Coefficient3
import SatFinal.PolynomialNumerics.Coefficient4
import SatFinal.PolynomialNumerics.Coefficient5
import SatFinal.PolynomialNumerics.Coefficient6
import SatFinal.PolynomialNumerics.Coefficient7
import SatFinal.PolynomialNumerics.Coefficient8
import SatFinal.PolynomialNumerics.Coefficient9
import SatFinal.PolynomialNumerics.Coefficient10
import SatFinal.PolynomialNumerics.Coefficient11
import SatFinal.PolynomialNumerics.Coefficient12
import SatFinal.PolynomialNumerics.Data
import SatFinal.PolynomialCoefficients
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SatFinal.PolynomialNumerics.Checks
open Data SatFinal.PolynomialBounds SatFinal.PolynomialCoefficients

theorem coefficient_identity : ∀ h : Fin 194,
    coefficients.getD (h.val+1) 0*(h.val+1 : ℚ) = rhsCoeff squareCoefficients h := by
  intro h
  have hh := h.isLt
  match he : h.val/16 with
  | 0 =>
    have hb := coefficient_block_0 ⟨h.val-0,by omega⟩
    have hc : (0 : ℚ)+((h.val-0 : ℕ) : ℚ) = (h.val : ℚ) := by
      exact_mod_cast (show 0+(h.val-0) = h.val by omega)
    simpa only [show 0+(h.val-0) = h.val by omega, hc] using hb
  | 1 =>
    have hb := coefficient_block_1 ⟨h.val-16,by omega⟩
    have hc : (16 : ℚ)+((h.val-16 : ℕ) : ℚ) = (h.val : ℚ) := by
      exact_mod_cast (show 16+(h.val-16) = h.val by omega)
    simpa only [show 16+(h.val-16) = h.val by omega, hc] using hb
  | 2 =>
    have hb := coefficient_block_2 ⟨h.val-32,by omega⟩
    have hc : (32 : ℚ)+((h.val-32 : ℕ) : ℚ) = (h.val : ℚ) := by
      exact_mod_cast (show 32+(h.val-32) = h.val by omega)
    simpa only [show 32+(h.val-32) = h.val by omega, hc] using hb
  | 3 =>
    have hb := coefficient_block_3 ⟨h.val-48,by omega⟩
    have hc : (48 : ℚ)+((h.val-48 : ℕ) : ℚ) = (h.val : ℚ) := by
      exact_mod_cast (show 48+(h.val-48) = h.val by omega)
    simpa only [show 48+(h.val-48) = h.val by omega, hc] using hb
  | 4 =>
    have hb := coefficient_block_4 ⟨h.val-64,by omega⟩
    have hc : (64 : ℚ)+((h.val-64 : ℕ) : ℚ) = (h.val : ℚ) := by
      exact_mod_cast (show 64+(h.val-64) = h.val by omega)
    simpa only [show 64+(h.val-64) = h.val by omega, hc] using hb
  | 5 =>
    have hb := coefficient_block_5 ⟨h.val-80,by omega⟩
    have hc : (80 : ℚ)+((h.val-80 : ℕ) : ℚ) = (h.val : ℚ) := by
      exact_mod_cast (show 80+(h.val-80) = h.val by omega)
    simpa only [show 80+(h.val-80) = h.val by omega, hc] using hb
  | 6 =>
    have hb := coefficient_block_6 ⟨h.val-96,by omega⟩
    have hc : (96 : ℚ)+((h.val-96 : ℕ) : ℚ) = (h.val : ℚ) := by
      exact_mod_cast (show 96+(h.val-96) = h.val by omega)
    simpa only [show 96+(h.val-96) = h.val by omega, hc] using hb
  | 7 =>
    have hb := coefficient_block_7 ⟨h.val-112,by omega⟩
    have hc : (112 : ℚ)+((h.val-112 : ℕ) : ℚ) = (h.val : ℚ) := by
      exact_mod_cast (show 112+(h.val-112) = h.val by omega)
    simpa only [show 112+(h.val-112) = h.val by omega, hc] using hb
  | 8 =>
    have hb := coefficient_block_8 ⟨h.val-128,by omega⟩
    have hc : (128 : ℚ)+((h.val-128 : ℕ) : ℚ) = (h.val : ℚ) := by
      exact_mod_cast (show 128+(h.val-128) = h.val by omega)
    simpa only [show 128+(h.val-128) = h.val by omega, hc] using hb
  | 9 =>
    have hb := coefficient_block_9 ⟨h.val-144,by omega⟩
    have hc : (144 : ℚ)+((h.val-144 : ℕ) : ℚ) = (h.val : ℚ) := by
      exact_mod_cast (show 144+(h.val-144) = h.val by omega)
    simpa only [show 144+(h.val-144) = h.val by omega, hc] using hb
  | 10 =>
    have hb := coefficient_block_10 ⟨h.val-160,by omega⟩
    have hc : (160 : ℚ)+((h.val-160 : ℕ) : ℚ) = (h.val : ℚ) := by
      exact_mod_cast (show 160+(h.val-160) = h.val by omega)
    simpa only [show 160+(h.val-160) = h.val by omega, hc] using hb
  | 11 =>
    have hb := coefficient_block_11 ⟨h.val-176,by omega⟩
    have hc : (176 : ℚ)+((h.val-176 : ℕ) : ℚ) = (h.val : ℚ) := by
      exact_mod_cast (show 176+(h.val-176) = h.val by omega)
    simpa only [show 176+(h.val-176) = h.val by omega, hc] using hb
  | 12 =>
    have hb := coefficient_block_12 ⟨h.val-192,by omega⟩
    have hc : (192 : ℚ)+((h.val-192 : ℕ) : ℚ) = (h.val : ℚ) := by
      exact_mod_cast (show 192+(h.val-192) = h.val by omega)
    simpa only [show 192+(h.val-192) = h.val by omega, hc] using hb
  | n+13 => omega

theorem polynomial_identity : (fromArray coefficients).derivative =
    2*fromArray squareCoefficients-(1-Polynomial.X)*(fromArray squareCoefficients)^2 := by
  apply identity coefficients squareCoefficients 193 (by decide +kernel) (by decide +kernel)
  intro h hh
  exact coefficient_identity ⟨h,by omega⟩

theorem polynomial_zero : (fromArray coefficients).eval 0 = 0 := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, array_coeff]
  norm_num [Array.getD, coefficients]

theorem polynomial_minorant : ∀ x ∈ Set.Ico (0 : ℝ) 1,
    (realPolynomial (fromArray coefficients)).eval x ≤ -Real.log (1-x) :=
  square_minorant _ _ polynomial_zero polynomial_identity

end SatFinal.PolynomialNumerics.Checks
