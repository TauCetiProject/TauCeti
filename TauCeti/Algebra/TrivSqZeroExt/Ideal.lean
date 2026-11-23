/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.TrivSqZeroExt.Ideal

/-!
# Complements on the square-zero ideal of a trivial square-zero extension

This file provides the ideal-product form of `TrivSqZeroExt.kerIdeal_sq`.

## Main results

* `TrivSqZeroExt.kerIdeal_mul_self`: `kerIdeal R M * kerIdeal R M = ⊥`.
-/

public section

namespace TrivSqZeroExt

/-- The kernel ideal of `TrivSqZeroExt.fstHom R R M` has product zero with itself. -/
theorem kerIdeal_mul_self (R M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M]
    [Module Rᵐᵒᵖ M] [IsCentralScalar R M] :
    kerIdeal R M * kerIdeal R M = ⊥ := by
  simpa only [pow_two] using kerIdeal_sq R M

end TrivSqZeroExt
