import SatFinal.PolynomialNumerics.Definitions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SatFinal.PolynomialNumerics.Checks
open SatKUpper Data CertificateBounds

theorem sizes : raw.size = 514 ∧ moments.size = 514 ∧ powers.size = 193 ∧
    nu.size = 193 ∧ arguments.size = 193 ∧ compound.size = 193 ∧ side.size = 193 := by decide +kernel

theorem coefficients_size : coefficients.size = 193 := by decide +kernel

theorem raw_initial : lower raw momentScale 0 ≤ 1 ∧ 1 ≤ upper raw momentScale 0 := by decide +kernel

theorem tail_step : (315/221 : ℚ)^3 * CertificateBounds.tailUpper a b tau (upper raw momentScale 513) 2 513 ≤
    (Data.tailUpper : ℚ)/finalScale := by decide +kernel

theorem rounded_upper :
    -(∑ h ∈ Finset.range 193, signedTerm h) + 2*alpha*
      ((∑ h ∈ Finset.range 512, term correctionTerms (h+1))+(Data.tailUpper : ℚ)/finalScale) ≤
        (totalUpper : ℚ)/finalScale := by decide +kernel

theorem final_margin :
    -(∑ h ∈ Finset.range 193, signedTerm h) + 2*alpha*
      ((∑ h ∈ Finset.range 512, term correctionTerms (h+1))+(Data.tailUpper : ℚ)/finalScale) ≤
        -(1/2500000000 : ℚ) := rounded_upper.trans (by decide +kernel)

theorem final_negative :
    -(∑ h ∈ Finset.range 193, signedTerm h) + 2*alpha*
      ((∑ h ∈ Finset.range 512, term correctionTerms (h+1))+(Data.tailUpper : ℚ)/finalScale) < 0 :=
  lt_of_le_of_lt final_margin (by norm_num)

end SatFinal.PolynomialNumerics.Checks
