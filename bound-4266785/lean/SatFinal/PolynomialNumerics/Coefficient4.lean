import SatFinal.PolynomialNumerics.Data
import SatFinal.PolynomialCoefficients
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SatFinal.PolynomialNumerics.Checks
open Data SatFinal.PolynomialCoefficients
theorem coefficient_block_4 : ∀ h : Fin 16,
    coefficients.getD (64+h.val+1) 0*(64+h.val+1 : ℚ) = rhsCoeff squareCoefficients (64+h.val) := by decide +kernel
end SatFinal.PolynomialNumerics.Checks
