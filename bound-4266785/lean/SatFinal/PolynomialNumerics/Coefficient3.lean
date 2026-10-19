import SatFinal.PolynomialNumerics.Data
import SatFinal.PolynomialCoefficients
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SatFinal.PolynomialNumerics.Checks
open Data SatFinal.PolynomialCoefficients
theorem coefficient_block_3 : ∀ h : Fin 16,
    coefficients.getD (48+h.val+1) 0*(48+h.val+1 : ℚ) = rhsCoeff squareCoefficients (48+h.val) := by decide +kernel
end SatFinal.PolynomialNumerics.Checks
