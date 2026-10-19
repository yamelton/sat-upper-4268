import SatFinal.PolynomialNumerics.Definitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SatFinal.PolynomialNumerics.Checks
theorem site_block_2 : ∀ j : Fin 64, siteStep (128+j.val) := by decide +kernel
end SatFinal.PolynomialNumerics.Checks
