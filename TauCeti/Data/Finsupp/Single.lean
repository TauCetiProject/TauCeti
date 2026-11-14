/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Single
public import Mathlib.Data.Int.Cast.Basic

/-!
# Casting the values of a single integer coefficient

The integer cast commutes with evaluating a finitely supported function with one-point support:
the cast of `Finsupp.single a n b` is `Finsupp.single a (n : R) b` in any additive group with one.
-/

public section

namespace Finsupp

/-- The cast of a value of `Finsupp.single a n` is the value of `Finsupp.single a (n : R)`. -/
@[simp, norm_cast]
theorem intCast_single_apply {α R : Type*} [AddGroupWithOne R] (a : α) (n : ℤ) (b : α) :
    ((single a n b : ℤ) : R) = single a (n : R) b :=
  apply_single' Int.cast Int.cast_zero a n b

end Finsupp
