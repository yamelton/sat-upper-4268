import SatFinal.Quadratic
import SatFinal.PolynomialNumerics.Data
import SatKUpper.CertificateBounds
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace SatFinal.PolynomialNumerics.Checks
open SatKUpper
open Data CertificateBounds

def term (xs : Array ℕ) (i : ℕ) : ℚ := (xs.getD i 0 : ℚ)/finalScale

abbrev rawStep (h : ℕ) : Prop :=
  lower raw momentScale (h+1) ≤ lower raw momentScale h * BetaEnclosures.ratio a b h ∧
  upper raw momentScale h * BetaEnclosures.ratio a b h ≤ upper raw momentScale (h+1)

abbrev momentStep (h : ℕ) : Prop :=
  lower moments momentScale h ≤ lower raw momentScale h * SatFinal.Quadratic.multiplier h ∧
  upper raw momentScale h * SatFinal.Quadratic.multiplier h ≤ upper moments momentScale h

abbrev powerStep (h : ℕ) : Prop :=
  0 ≤ lower moments momentScale h ∧
  lower powers momentScale h ≤ (lower moments momentScale h)^2 ∧
  (upper moments momentScale h)^2 ≤ upper powers momentScale h

abbrev argumentStep (h : ℕ) : Prop :=
  lower arguments argumentScale h ≤ (3*alpha/2)*(lower nu momentScale h-1) ∧
  (3*alpha/2)*(upper nu momentScale h-1) ≤ upper arguments argumentScale h ∧
  -(2 : ℚ)^squarings ≤ lower arguments argumentScale h ∧
  lower arguments argumentScale h ≤ 0 ∧ upper arguments argumentScale h ≤ 0

abbrev expStep (h : ℕ) : Prop :=
  let p := TaylorExponential.bounds internalScale terms squarings (lower arguments argumentScale h)
  lower compound expScale h ≤ p.1 ∧
    p.2+(upper arguments argumentScale h-lower arguments argumentScale h) ≤ upper compound expScale h

def signedTerm (h : ℕ) : ℚ := (siteTerms.getD h 0 : ℚ)/finalScale

def coefficient (h : ℕ) : ℚ := coefficients.getD h 0

abbrev siteStep (h : ℕ) : Prop :=
  0 ≤ lower side expScale h ∧
  signedTerm h ≤ coefficient h * (if 0 ≤ coefficient h then lower side expScale h else upper side expScale h)^2

abbrev correctionStep (h : ℕ) : Prop :=
  (upper moments momentScale (h+1))^3/(h+1) ≤ term correctionTerms (h+1)

end SatFinal.PolynomialNumerics.Checks
