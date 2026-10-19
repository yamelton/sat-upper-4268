import SatKUpper.Moments

/-! Round a coin in [0,1) down to a finite grid. Every moment is dominated
by the original moment and converges to it. In particular, approximation
cannot increase the positive correction series. -/

open MeasureTheory SatKUpper.Sampling

namespace SatKUpper.FiniteApproximation

abbrev Coin := {x : ℝ // 0 ≤ x ∧ x < 1}

noncomputable def index (d : ℕ) (x : Coin) : Fin (d+1) :=
  ⟨⌊(d+1 : ℝ)*x.val⌋₊, (Nat.floor_lt (mul_nonneg (by positivity) x.property.1)).mpr
    (by exact_mod_cast mul_lt_of_lt_one_right (by positivity : (0 : ℝ) < d+1) x.property.2)⟩

theorem measurable_floor : Measurable (Nat.floor : ℝ → ℕ) := by
  apply measurable_to_countable
  intro n
  rcases eq_or_ne ⌊n⌋₊ 0 with h | h <;>
    simp [h, Nat.preimage_floor_of_ne_zero, -Nat.floor_eq_zero]

theorem measurable_index (d : ℕ) : Measurable (index d) := by
  apply measurable_to_countable
  intro i
  have hf : Measurable (fun x : Coin => ⌊(d+1 : ℝ)*x.val⌋₊) :=
    measurable_floor.comp (measurable_const.mul measurable_subtype_coe)
  have h := hf (t := {(index d i).val}) (measurableSet_singleton (index d i).val)
  convert h using 1
  ext x
  simp [index, Fin.ext_iff]

noncomputable def rounded (d : ℕ) (x : Coin) : ℝ := (index d x).val/(d+1 : ℝ)

theorem rounded_bounds (d : ℕ) (x : Coin) :
    0 ≤ rounded d x ∧ rounded d x ≤ x.val ∧ x.val-rounded d x ≤ 1/(d+1 : ℝ) := by
  have hd : (0 : ℝ) < d+1 := by positivity
  have hl := Nat.floor_le (mul_nonneg hd.le x.property.1)
  have hu := Nat.lt_floor_add_one ((d+1 : ℝ)*x.val)
  unfold rounded index
  dsimp only
  refine ⟨by positivity, (div_le_iff₀ hd).mpr (by nlinarith), ?_⟩
  apply (le_div_iff₀ hd).mpr
  rw [sub_mul, div_mul_cancel₀ _ hd.ne']
  nlinarith

theorem rounded_tendsto (x : Coin) :
    Filter.Tendsto (fun d : ℕ => rounded d x) Filter.atTop (nhds x.val) := by
  have ht : Filter.Tendsto (fun d : ℕ => 1/(d+1 : ℝ)) Filter.atTop (nhds 0) := by
    simp only [one_div]
    apply tendsto_inv_atTop_zero.comp
    exact Filter.tendsto_atTop_mono (fun d : ℕ => show (d : ℝ) ≤ d+1 by linarith)
      tendsto_natCast_atTop_atTop
  have hz := squeeze_zero (fun d => sub_nonneg.mpr (rounded_bounds d x).2.1)
    (fun d => (rounded_bounds d x).2.2) ht
  have hc : Filter.Tendsto (fun _ : ℕ => x.val) Filter.atTop (nhds x.val) := tendsto_const_nhds
  simpa only [sub_zero, sub_sub_cancel] using hc.sub hz

variable (μ : Measure Coin) [IsProbabilityMeasure μ]

noncomputable def law (d : ℕ) : CoinLaw (d+1) where
  measure := Measure.map (index d) μ
  probability := Measure.isProbabilityMeasure_map (measurable_index d).aemeasurable
  rate := fun i => (i.val : ℝ)/(d+1 : ℝ)
  nonneg := fun _ => by positivity
  lt_one := fun i => (div_lt_one (by positivity)).mpr (by exact_mod_cast i.isLt)

theorem moment_eq (d h : ℕ) :
    Moments.moment (law μ d) h = ∫ x, rounded d x ^ h ∂μ := by
  unfold Moments.moment law
  rw [integral_map (measurable_index d).aemeasurable
    (measurable_of_countable _).aestronglyMeasurable]
  rfl

theorem rounded_measurable (d : ℕ) : Measurable (rounded d) := by
  exact (measurable_of_countable (fun i : Fin (d+1) =>
    (i.val : ℝ)/(d+1 : ℝ))).comp (measurable_index d)

theorem moment_le (d h : ℕ) :
    Moments.moment (law μ d) h ≤ ∫ x : Coin, x.val ^ h ∂μ := by
  rw [moment_eq]
  apply integral_mono
    (SatUpper.ReplicaMoments.integrable_unit_interval μ ((rounded_measurable d).pow_const h)
      (fun x => pow_nonneg (rounded_bounds d x).1 h)
      (fun x => pow_le_one₀ (rounded_bounds d x).1
        ((rounded_bounds d x).2.1.trans x.property.2.le)))
    (SatUpper.ReplicaMoments.integrable_unit_interval μ (measurable_subtype_coe.pow_const h)
      (fun x => pow_nonneg x.property.1 h)
      (fun x => pow_le_one₀ x.property.1 x.property.2.le))
  intro x
  exact pow_le_pow_left₀ (rounded_bounds d x).1 (rounded_bounds d x).2.1 h

theorem moment_tendsto (h : ℕ) :
    Filter.Tendsto (fun d => Moments.moment (law μ d) h) Filter.atTop
      (nhds (∫ x : Coin, x.val ^ h ∂μ)) := by
  simp_rw [moment_eq]
  apply tendsto_integral_of_dominated_convergence (fun _ => 1)
    (fun d => ((rounded_measurable d).pow_const h).aestronglyMeasurable) (integrable_const _)
  · intro d
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (rounded_bounds d x).1 h)]
    exact pow_le_one₀ (rounded_bounds d x).1 ((rounded_bounds d x).2.1.trans x.property.2.le)
  · filter_upwards [] with x
    exact (rounded_tendsto x).pow h

end SatKUpper.FiniteApproximation
