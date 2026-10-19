import SatFinal.PolynomialNumerics.Definitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SatFinal.PolynomialNumerics.Checks
theorem correction_block_4 : ∀ j : Fin 64, correctionStep (256+j.val) := by decide +kernel
end SatFinal.PolynomialNumerics.Checks
