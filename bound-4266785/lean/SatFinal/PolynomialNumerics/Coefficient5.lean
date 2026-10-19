import SatFinal.PolynomialNumerics.Data
import SatFinal.PolynomialCoefficients
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SatFinal.PolynomialNumerics.Checks
open Data SatFinal.PolynomialCoefficients
theorem coefficient_block_5 : ∀ h : Fin 16,
    coefficients.getD (80+h.val+1) 0*(80+h.val+1 : ℚ) = rhsCoeff squareCoefficients (80+h.val) := by decide +kernel
end SatFinal.PolynomialNumerics.Checks
