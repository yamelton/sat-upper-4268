import SatFinal.PolynomialNumerics.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SatFinal.PolynomialNumerics.Checks
open Data SatKUpper.DifferenceEnclosures
theorem nu_table : table 193 powers.toList = nu.toList := by decide +kernel
theorem side_table : table 193 compound.toList = side.toList := by decide +kernel
end SatFinal.PolynomialNumerics.Checks
