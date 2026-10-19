import SatKUpper.SiteBound
import SatKUpper.EdgeBound
import SatKUpper.DePoissonization

/-! One finite-law criterion for every positive clause size. Its conclusion
is the limiting satisfiability probability in the distinct-variable model. -/

open SatUpper SatKUpper.Sampling SatKUpper.SiteProducts
open scoped NNReal

namespace SatKUpper.Criterion

noncomputable def value {t : ℕ} (law : CoinLaw t) (r : ℕ) (α : ℝ) (T : ℕ) : ℝ :=
  negativeMomentSum T (complementMoment law r ((r+1 : ℝ)*α/2)) +
    (r : ℝ)*α*EdgeBound.correction law r

theorem poisson_bound {t r n : ℕ} [NeZero n] (law : CoinLaw t)
    (α : ℝ≥0) (T : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    (-y/n)*ClauseEndpoint.poissonMean (r+1) n (α*n) ≤
      value law r α T + (T : ℝ)*Real.exp (-y) := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have he := ClauseEndpoint.energy_comparison (r := r) (n := n) law hy (α*n)
  have hs := SiteBound.endpoint (r := r) (n := n) law hy ((r+1)*(α*n)) T
  have hm : (((r+1)*(α*n) : ℝ≥0) : ℝ)/(2*n) = (r+1 : ℝ)*α/2 := by
    simp only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]
    field_simp
  rw [hm] at hs
  have hc := mul_le_mul_of_nonneg_left (EdgeBound.edge_le (r := r) (n := n) law y)
    (show 0 ≤ (r : ℝ)*(α*n : ℝ≥0) by positivity)
  have h := he.trans (sub_le_sub hs hc)
  simp only [NNReal.coe_mul, NNReal.coe_natCast] at h
  have hd := div_le_div_of_nonneg_right h hn.le
  convert hd using 1
  · ring
  · simp only [value, negativeMomentSum]
    field_simp
    ring

theorem upperBound {t r : ℕ} (law : CoinLaw t) (α : ℝ≥0) (T : ℕ)
    (h : value law r α T < 0) : Model.UpperBound (r+1) α := by
  apply DePoissonization.upperBound_of_poisson_bound law α T h
  intro n hn y hy
  letI : NeZero n := ⟨by omega⟩
  exact poisson_bound law α T hy.le

end SatKUpper.Criterion
