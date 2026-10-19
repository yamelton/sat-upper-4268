import SatFinal.PolynomialNumerics.Definitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SatFinal.PolynomialNumerics.Checks
theorem correction_block_3 : ∀ j : Fin 64, correctionStep (192+j.val) := by decide +kernel
end SatFinal.PolynomialNumerics.Checks
