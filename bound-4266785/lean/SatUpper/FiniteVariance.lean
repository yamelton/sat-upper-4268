import SatUpper.Concentration
import Mathlib.Algebra.BigOperators.Field

/-! Finite-product variance bounds from single-coordinate changes. -/

namespace SatUpper.FiniteVariance

variable {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]

theorem average_const [Nonempty Ω] (c : ℝ) : uniformAverage (fun _ : Ω => c) = c := by
  simp [uniformAverage, Fintype.card_ne_zero]

theorem average_add (f g : Ω → ℝ) :
    uniformAverage (fun x => f x + g x) = uniformAverage f + uniformAverage g := by
  simp only [uniformAverage, Finset.sum_add_distrib, add_div]

theorem average_sub (f g : Ω → ℝ) :
    uniformAverage (fun x => f x - g x) = uniformAverage f - uniformAverage g := by
  simp only [uniformAverage, Finset.sum_sub_distrib, sub_div]

theorem average_const_mul (c : ℝ) (f : Ω → ℝ) :
    uniformAverage (fun x => c * f x) = c * uniformAverage f := by
  simp only [uniformAverage, ← Finset.mul_sum, mul_div_assoc]

theorem average_mono {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) :
    uniformAverage f ≤ uniformAverage g := by
  apply div_le_div_of_nonneg_right
    (Finset.sum_le_sum (fun x _ => h x)) (Nat.cast_nonneg _)

theorem average_equiv (e : Ω ≃ Λ) (f : Λ → ℝ) :
    uniformAverage (fun x => f (e x)) = uniformAverage f := by
  unfold uniformAverage
  rw [Fintype.card_congr e, e.sum_comp f]

theorem average_prod (f : Ω × Λ → ℝ) :
    uniformAverage f = uniformAverage (fun x => uniformAverage (fun y => f (x, y))) := by
  simp only [uniformAverage, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    ← Finset.sum_div, div_div]
  congr 1
  ring

theorem variance_second_moment [Nonempty Ω] (f : Ω → ℝ) :
    uniformVariance f = uniformAverage (fun x => (f x) ^ 2) - (uniformAverage f) ^ 2 := by
  have he : (fun x => (f x - uniformAverage f) ^ 2) =
      (fun x => (f x) ^ 2 - (2 * uniformAverage f) * f x + (uniformAverage f) ^ 2) := by
    funext x
    ring
  rw [uniformVariance, he, average_add, average_sub, average_const_mul, average_const]
  ring

theorem average_sq_center [Nonempty Ω] (f : Ω → ℝ) (c : ℝ) :
    uniformAverage (fun x => (f x - c) ^ 2) = uniformVariance f + (uniformAverage f - c) ^ 2 := by
  have he : (fun x => (f x - c) ^ 2) = (fun x => (f x) ^ 2 - (2 * c) * f x + c ^ 2) := by
    funext x
    ring
  rw [he, average_add, average_sub, average_const_mul, average_const, variance_second_moment]
  ring

theorem variance_le_center [Nonempty Ω] (f : Ω → ℝ) (c : ℝ) :
    uniformVariance f ≤ uniformAverage (fun x => (f x - c) ^ 2) := by
  rw [average_sq_center]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- A range of diameter at most `C` gives variance at most `C^2`. -/
theorem variance_le_of_diameter [Nonempty Ω] (f : Ω → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x y, |f x - f y| ≤ C) : uniformVariance f ≤ C ^ 2 := by
  let y : Ω := Classical.arbitrary Ω
  calc
    uniformVariance f ≤ uniformAverage (fun x => (f x - f y) ^ 2) := variance_le_center f (f y)
    _ ≤ uniformAverage (fun _ : Ω => C ^ 2) := average_mono fun x => by
      have hh := (sq_le_sq₀ (abs_nonneg (f x - f y)) hC).mpr (h x y)
      simpa only [sq_abs] using hh
    _ = _ := average_const _

/-- Total variance for a uniform product: average conditional variance plus
variance of the conditional mean. -/
theorem variance_prod [Nonempty Ω] [Nonempty Λ] (f : Ω × Λ → ℝ) :
    uniformVariance f =
      uniformAverage (fun x => uniformVariance (fun y => f (x, y))) +
      uniformVariance (fun x => uniformAverage (fun y => f (x, y))) := by
  rw [variance_second_moment, average_prod, average_prod]
  simp_rw [variance_second_moment]
  rw [average_sub]
  ring

theorem variance_equiv (e : Ω ≃ Λ) (f : Λ → ℝ) :
    uniformVariance (fun x => f (e x)) = uniformVariance f := by
  unfold uniformVariance
  rw [average_equiv e f]
  exact average_equiv e (fun y => (f y - uniformAverage f) ^ 2)

theorem abs_average_sub_le [Nonempty Ω] (f g : Ω → ℝ) {C : ℝ}
    (h : ∀ x, |f x - g x| ≤ C) : |uniformAverage f - uniformAverage g| ≤ C := by
  rw [← average_sub]
  apply abs_le.mpr
  constructor
  · calc
      -C = uniformAverage (fun _ : Ω => -C) := (average_const _).symm
      _ ≤ _ := average_mono fun x => (abs_le.mp (h x)).1
  · calc
      _ ≤ uniformAverage (fun _ : Ω => C) := average_mono fun x => (abs_le.mp (h x)).2
      _ = C := average_const _

/-- Independent finite coordinates with change bound `C` have variance
at most the number of coordinates times `C^2`. -/
theorem variance_fin_pi_le [Nonempty Ω] (M : ℕ) (f : (Fin M → Ω) → ℝ)
    {C : ℝ} (hC : 0 ≤ C)
    (hchange : ∀ x y j, (∀ i, i ≠ j → x i = y i) → |f x - f y| ≤ C) :
    uniformVariance f ≤ (M : ℝ) * C ^ 2 := by
  classical
  induction M with
  | zero =>
    have he : f = fun _ => f (fun i => Fin.elim0 i) := by
      funext x
      congr 1
      funext i
      exact Fin.elim0 i
    rw [he]
    simp [uniformVariance, average_const]
  | succ M ih =>
    let F : Ω × (Fin M → Ω) → ℝ := fun p => f (Fin.cons p.1 p.2)
    have he : uniformVariance f = uniformVariance F :=
      (variance_equiv (Fin.consEquiv (fun _ : Fin (M + 1) => Ω)) f).symm
    rw [he, variance_prod]
    have htail (a : Ω) : uniformVariance (fun x : Fin M → Ω => F (a, x)) ≤ (M : ℝ) * C ^ 2 := by
      apply ih
      intro x y j hxy
      apply hchange (Fin.cons a x) (Fin.cons a y) j.succ
      intro i
      refine Fin.cases ?_ (fun k => ?_) i
      · intro _
        rfl
      · intro hk
        simp only [Fin.cons_succ]
        exact hxy k (fun h => hk (congrArg Fin.succ h))
    have hhead : uniformVariance (fun a : Ω => uniformAverage (fun x : Fin M → Ω => F (a, x))) ≤ C ^ 2 := by
      apply variance_le_of_diameter _ hC
      intro a b
      apply abs_average_sub_le
      intro x
      apply hchange (Fin.cons a x) (Fin.cons b x) 0
      intro i
      refine Fin.cases ?_ (fun k => ?_) i
      · intro hi
        exact (hi rfl).elim
      · intro _
        rfl
    calc
      _ ≤ uniformAverage (fun _ : Ω => (M : ℝ) * C ^ 2) + C ^ 2 :=
        add_le_add (average_mono htail) hhead
      _ = ((M + 1 : ℕ) : ℝ) * C ^ 2 := by rw [average_const]; push_cast; ring

end SatUpper.FiniteVariance
