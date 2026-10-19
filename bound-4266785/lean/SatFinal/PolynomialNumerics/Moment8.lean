import SatFinal.PolynomialNumerics.Definitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SatFinal.PolynomialNumerics.Checks
theorem moment_block_8 : ∀ j : Fin 2, momentStep (512+j.val) := by decide +kernel
end SatFinal.PolynomialNumerics.Checks
