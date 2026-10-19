import SatFinal.PolynomialNumerics.Definitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SatFinal.PolynomialNumerics.Checks
theorem moment_block_4 : ∀ j : Fin 64, momentStep (256+j.val) := by decide +kernel
end SatFinal.PolynomialNumerics.Checks
