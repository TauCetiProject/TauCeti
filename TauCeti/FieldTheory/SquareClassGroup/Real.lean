/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import TauCeti.Algebra.Group.Units.Basic
public import TauCeti.FieldTheory.SquareClassGroup.Basic

/-!
# Square classes of real numbers

A nonzero real number is a square exactly when it is positive, so the square-class group of `ℝ`
has two elements: the trivial class and the class of `-1`.  This file records that description in
the form used to read signs off square-class invariants such as the discriminant of a quadratic
form.

## Main results

* `TauCeti.squareClass_eq_zero_iff_pos`: a real unit has trivial square class iff it is positive.
* `TauCeti.squareClass_eq_squareClass_neg_one_of_neg`: every negative real unit has the square
  class of `-1`.
* `TauCeti.sum_squareClass_eq_ncard_nsmul`: the square classes of a finite family of real units
  add up to the number of negative members times the class of `-1`.
* `TauCeti.nsmul_squareClass_neg_one_eq_zero_iff_even`: `n • [-1]` vanishes in the real
  square-class group exactly when `n` is even.
-/

public section

namespace TauCeti

/-- A real unit has trivial square class exactly when it is positive. -/
theorem squareClass_eq_zero_iff_pos (u : ℝˣ) : squareClass u = 0 ↔ 0 < (u : ℝ) := by
  rw [squareClass_eq_zero_iff, ← isSquare_units_val_iff, Real.isSquare_iff]
  exact ⟨fun h ↦ lt_of_le_of_ne h (Units.ne_zero u).symm, le_of_lt⟩

/-- A negative real unit has the square class of `-1`. -/
theorem squareClass_eq_squareClass_neg_one_of_neg {u : ℝˣ} (hu : (u : ℝ) < 0) :
    squareClass u = squareClass (-1 : ℝˣ) := by
  rw [squareClass_eq_iff_isSquare_mul, ← isSquare_units_val_iff, Real.isSquare_iff]
  simpa using hu.le

/-- The `n`-th multiple of the square class of `-1` in the real square-class group vanishes
exactly when `n` is even. -/
@[simp]
theorem nsmul_squareClass_neg_one_eq_zero_iff_even (n : ℕ) :
    n • squareClass (-1 : ℝˣ) = 0 ↔ Even n := by
  rw [← squareClass_pow, squareClass_eq_zero_iff_pos, Units.val_pow_eq_pow_val, Units.val_neg,
    Units.val_one]
  rcases n.even_or_odd with hn | hn
  · simp [hn, hn.neg_one_pow]
  · simp [hn.neg_one_pow, Nat.not_even_iff_odd.mpr hn]

/-- The square classes of a finite family of real units add up to the number of negative members
times the class of `-1`. -/
theorem sum_squareClass_eq_ncard_nsmul {ι : Type*} [Fintype ι] (w : ι → ℝˣ) :
    ∑ i, squareClass (w i) = {i | (w i : ℝ) < 0}.ncard • squareClass (-1 : ℝˣ) := by
  classical
  have hterm : ∀ i, squareClass (w i) =
      if (w i : ℝ) < 0 then squareClass (-1 : ℝˣ) else 0 := fun i ↦ by
    split_ifs with hi
    · exact squareClass_eq_squareClass_neg_one_of_neg hi
    · exact (squareClass_eq_zero_iff_pos _).mpr
        (lt_of_le_of_ne (not_lt.mp hi) (Units.ne_zero (w i)).symm)
  rw [Finset.sum_congr rfl fun i _ ↦ hterm i, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, ← Set.ncard_coe_finset]
  simp

end TauCeti
