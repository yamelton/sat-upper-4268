import SatKUpper.FiniteDifferences

/-! Integer interval tables for both binomial transforms. All entries use
one common scale, so the triangular calculation needs only subtraction. -/

namespace SatKUpper.DifferenceEnclosures

abbrev Interval := ℤ × ℤ

def next : List Interval → List Interval
  | a::b::xs => (a.1-b.2,a.2-b.1)::next (b::xs)
  | _ => []

theorem next_length (xs : List Interval) : (next xs).length = xs.length-1 := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases xs with
    | nil => rfl
    | cons b xs => simpa [next] using ih

theorem next_get (xs : List Interval) (i : ℕ) (hi : i+1 < xs.length) :
    (next xs).getD i (0,0) =
      ((xs.getD i (0,0)).1-(xs.getD (i+1) (0,0)).2,
       (xs.getD i (0,0)).2-(xs.getD (i+1) (0,0)).1) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    cases xs with
    | nil => simp at hi
    | cons b xs =>
      cases i with
      | zero => rfl
      | succ i =>
        simpa [next] using ih i (by simpa using hi)

def Encloses (scale : ℝ) (xs : List Interval) (f : ℕ → ℝ) : Prop :=
  ∀ i, i < xs.length → ((xs.getD i (0,0)).1 : ℝ) ≤ scale*f i ∧
    scale*f i ≤ ((xs.getD i (0,0)).2 : ℝ)

theorem next_correct {scale : ℝ} {xs : List Interval} {f : ℕ → ℝ}
    (h : Encloses scale xs f) : Encloses scale (next xs) (fun i => f i-f (i+1)) := by
  intro i hi
  have hi' : i+1 < xs.length := by rw [next_length] at hi; omega
  have h0 := h i (by omega)
  have h1 := h (i+1) hi'
  rw [next_get xs i hi']
  push_cast
  constructor <;> nlinarith

def table : ℕ → List Interval → List Interval
  | 0, _ => []
  | n+1, xs => xs.headD (0,0)::table n (next xs)

theorem table_length (n : ℕ) (xs : List Interval) : (table n xs).length = n := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih => simp [table, ih]

theorem table_correct {scale : ℝ} {xs : List Interval} {f : ℕ → ℝ}
    (h : Encloses scale xs f) (n : ℕ) (hn : n ≤ xs.length) :
    Encloses scale (table n xs) (fun i => FiniteDifferences.difference f i 0) := by
  induction n generalizing xs f with
  | zero => intro i hi; simp [table] at hi
  | succ n ih =>
    have ht := ih (next_correct h) (by rw [next_length]; omega)
    intro i hi
    rw [table_length] at hi
    cases i with
    | zero =>
      have hb := h 0 (by omega)
      cases xs <;> simpa [table, FiniteDifferences.difference] using hb
    | succ i =>
      have hb := ht i (by rw [table_length]; omega)
      simpa [table, FiniteDifferences.difference_shift] using hb

end SatKUpper.DifferenceEnclosures
