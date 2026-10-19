import SatFinal.PolynomialNumerics.Definitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SatFinal.PolynomialNumerics.Checks
theorem raw_block_5 : ∀ j : Fin 64, rawStep (320+j.val) := by decide +kernel
end SatFinal.PolynomialNumerics.Checks
