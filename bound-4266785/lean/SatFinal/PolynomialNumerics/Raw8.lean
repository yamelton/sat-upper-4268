import SatFinal.PolynomialNumerics.Definitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SatFinal.PolynomialNumerics.Checks
theorem raw_block_8 : ∀ j : Fin 1, rawStep (512+j.val) := by decide +kernel
end SatFinal.PolynomialNumerics.Checks
