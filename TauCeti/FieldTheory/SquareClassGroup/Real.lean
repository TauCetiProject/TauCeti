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

* `Units.isSquare_iff_pos`: a real unit is a square iff it is positive.
* `Units.squareClass_eq_zero_iff_pos`: a real unit has trivial square class iff it is positive.
* `Units.squareClass_eq_squareClass_neg_one_iff_neg`: a real unit has the square class of `-1`
  iff it is negative.
* `TauCeti.sum_squareClass_eq_ncard_nsmul`: the square classes of a finite family of real units
  add up to the number of negative members times the class of `-1`.
* `TauCeti.nsmul_squareClass_neg_one_eq_zero_iff_even`: `n • [-1]` vanishes in the real
  square-class group exactly when `n` is even.
* `TauCeti.eq_one_or_eq_squareClassHom_neg_one`: every real square class is either the trivial
  class or the class of `-1`, in multiplicative notation.
-/

public section

open TauCeti

namespace Units

/-- A real unit is a square exactly when it is positive. -/
@[simp]
theorem isSquare_iff_pos (u : ℝˣ) : IsSquare u ↔ 0 < (u : ℝ) := by
  rw [← isSquare_units_val_iff, Real.isSquare_iff]
  exact ⟨fun h ↦ lt_of_le_of_ne h (Units.ne_zero u).symm, le_of_lt⟩

/-- A real unit has trivial square class exactly when it is positive.

This is not tagged `@[simp]` because `squareClass_eq_zero_iff` rewrites its left-hand side first;
`Units.isSquare_iff_pos` supplies the resulting simp-normal rule. -/
theorem squareClass_eq_zero_iff_pos (u : ℝˣ) : squareClass u = 0 ↔ 0 < (u : ℝ) := by
  rw [squareClass_eq_zero_iff, isSquare_iff_pos]

/-- A real unit has the square class of `-1` exactly when it is negative. -/
@[simp]
theorem squareClass_eq_squareClass_neg_one_iff_neg (u : ℝˣ) :
    squareClass u = squareClass (-1 : ℝˣ) ↔ (u : ℝ) < 0 := by
  rw [squareClass_eq_iff_isSquare_mul, ← isSquare_units_val_iff, Real.isSquare_iff]
  simp only [Units.val_neg, mul_neg, mul_one]
  constructor
  · exact fun h ↦ lt_of_le_of_ne (neg_nonneg.mp h) (Units.ne_zero u)
  · exact fun h ↦ neg_nonneg.mpr h.le

end Units

namespace TauCeti

/-- The `n`-th multiple of the square class of `-1` in the real square-class group vanishes
exactly when `n` is even. -/
@[simp]
theorem nsmul_squareClass_neg_one_eq_zero_iff_even (n : ℕ) :
    n • squareClass (-1 : ℝˣ) = 0 ↔ Even n := by
  rw [← squareClass_pow, Units.squareClass_eq_zero_iff_pos, Units.val_pow_eq_pow_val,
    Units.val_neg, Units.val_one]
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
    · exact (Units.squareClass_eq_squareClass_neg_one_iff_neg _).mpr hi
    · exact (Units.squareClass_eq_zero_iff_pos _).mpr
        (lt_of_le_of_ne (not_lt.mp hi) (Units.ne_zero (w i)).symm)
  rw [Finset.sum_congr rfl fun i _ ↦ hterm i, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, ← Set.ncard_coe_finset]
  simp

private theorem ofAdd_mk_ofMul (u : ℝˣ) :
    Multiplicative.ofAdd (QuotientAddGroup.mk (Additive.ofMul u)) = squareClassHom u := by
  rw [squareClassHom_apply, squareClass_def]

private theorem squareClassHom_eq_one_or_eq_squareClassHom_neg_one (u : ℝˣ) :
    squareClassHom u = 1 ∨ squareClassHom u = squareClassHom (-1 : ℝˣ) := by
  rcases lt_or_gt_of_ne (Units.ne_zero u) with hu | hu
  · refine Or.inr ?_
    rw [squareClassHom_apply, squareClassHom_apply,
      (Units.squareClass_eq_squareClass_neg_one_iff_neg u).mpr hu]
  · refine Or.inl ?_
    rw [squareClassHom_apply, (Units.squareClass_eq_zero_iff_pos u).mpr hu]
    rfl

/-- Every real square class is either the trivial class or the class of `-1`. -/
theorem eq_one_or_eq_squareClassHom_neg_one (x : Multiplicative (SquareClassGroup ℝ)) :
    x = 1 ∨ x = squareClassHom (-1 : ℝˣ) := by
  refine Multiplicative.rec ?_ x
  intro y
  obtain ⟨a, ha⟩ := QuotientAddGroup.mk_surjective (y : SquareClassGroup ℝ)
  rw [← ha]
  obtain ⟨u, rfl⟩ := (Additive.ofMul.surjective a)
  simpa only [ofAdd_mk_ofMul] using squareClassHom_eq_one_or_eq_squareClassHom_neg_one u

end TauCeti
