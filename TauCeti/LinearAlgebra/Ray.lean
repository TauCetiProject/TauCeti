/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Ray

/-!
# Sums of vectors in the same ray

Two nonzero vectors in the same ray cannot cancel: their sum is again nonzero. This is the
non-degeneracy needed to merge adjacent segments of a piecewise-linear path that point in the same
direction.
-/

public section

open Module

variable {R M : Type*} [CommRing R] [PartialOrder R] [IsStrictOrderedRing R] [IsDomain R]
  [AddCommGroup M] [Module R M] [IsTorsionFree R M] {x y : M}

/-- The sum of two vectors in the same ray, the first of them nonzero, is nonzero. -/
theorem SameRay.add_ne_zero (h : SameRay R x y) (hx : x ≠ 0) : x + y ≠ 0 := by
  intro hxy
  rw [add_eq_zero_iff_eq_neg'] at hxy
  exact hx (eq_zero_of_sameRay_self_neg (hxy ▸ h))
