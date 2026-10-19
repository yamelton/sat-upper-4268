import SatFinal.PolynomialNumerics.Definitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SatFinal.PolynomialNumerics.Checks
theorem exp_block_10 : ∀ j : Fin 8, expStep (80+j.val) := by decide +kernel
end SatFinal.PolynomialNumerics.Checks
