/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Data.Int.Cast.Basic

/-!
# Single-point finitely supported functions

The integer cast commutes with evaluating a finitely supported function with one-point support:
the cast of `Finsupp.single a n b` is `Finsupp.single a (n : R) b` in any additive group with one.
Sums of two `Finsupp.single` terms at distinct coordinates `i ≠ j` determine both coefficients
unconditionally (`Finsupp.single_add_single_eq_single_add_single_iff`).
-/

public section

namespace Finsupp

/-- The cast of a value of `Finsupp.single a n` is the value of `Finsupp.single a (n : R)`. -/
@[simp, norm_cast]
theorem intCast_single_apply {α R : Type*} [AddGroupWithOne R] (a : α) (n : ℤ) (b : α) :
    ((single a n b : ℤ) : R) = single a (n : R) b :=
  apply_single' Int.cast Int.cast_zero a n b

/-- A sum of two `Finsupp.single`s at distinct coordinates `i ≠ j` determines both coefficients,
without assuming either coefficient is nonzero. -/
theorem single_add_single_eq_single_add_single_iff {α M : Type*} [AddZeroClass M]
    {i j : α} (hij : i ≠ j) {a b c d : M} :
    single i a + single j b = single i c + single j d ↔ a = c ∧ b = d := by
  classical
  constructor
  · intro h
    have hi := DFunLike.congr_fun h i
    have hj := DFunLike.congr_fun h j
    simp only [coe_add, Pi.add_apply, single_eq_same, single_eq_of_ne hij,
      single_eq_of_ne hij.symm, add_zero, zero_add] at hi hj
    exact ⟨hi, hj⟩
  · rintro ⟨rfl, rfl⟩
    rfl

end Finsupp
