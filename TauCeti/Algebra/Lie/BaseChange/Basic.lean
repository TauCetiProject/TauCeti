/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.BaseChange

/-!
# Lie brackets and the scalar-restriction identification

The additive identification between a scalar-restricted Lie ring and its original carrier
preserves brackets. This is the bracket inherited by Mathlib's scalar-restriction type alias.

## References

* `Mathlib.Algebra.Lie.BaseChange`, for the inherited Lie-ring structure on `RestrictScalars`.
-/

public section

/-- The additive identification for scalar restriction preserves the Lie bracket. -/
@[simp]
theorem RestrictScalars.addEquiv_lie {R A L : Type*} [LieRing L]
    (x y : RestrictScalars R A L) :
    RestrictScalars.addEquiv R A L ⁅x, y⁆ =
      ⁅RestrictScalars.addEquiv R A L x, RestrictScalars.addEquiv R A L y⁆ := rfl
