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
direction. A vector lies in the same ray as such a sum exactly when it lies in the same ray as the
summands, since `SameRay` is transitive through a nonzero vector.
-/

public section

open Module

section Semiring

variable {R M : Type*} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
  [AddCommMonoid M] [Module R M] {x y z : M}

/-- `SameRay` is transitive through a nonzero vector. -/
theorem SameRay.trans_of_ne_zero (hxy : SameRay R x y) (hyz : SameRay R y z) (hy : y ≠ 0) :
    SameRay R x z :=
  hxy.trans hyz fun h ↦ absurd h hy

end Semiring

variable {R M : Type*} [CommRing R] [PartialOrder R] [IsStrictOrderedRing R] [IsDomain R]
  [AddCommGroup M] [Module R M] [IsTorsionFree R M] {x y z : M}

/-- The sum of two vectors in the same ray, the first of them nonzero, is nonzero. -/
theorem SameRay.add_ne_zero (h : SameRay R x y) (hx : x ≠ 0) : x + y ≠ 0 := by
  intro hxy
  rw [add_eq_zero_iff_eq_neg'] at hxy
  exact hx (eq_zero_of_sameRay_self_neg (hxy ▸ h))

/-- If `x` and `y` lie in the same ray and `y` is nonzero, then a vector lies in the same ray as
`x + y` exactly when it lies in the same ray as `y`. -/
theorem SameRay.sameRay_add_left_iff (h : SameRay R x y) (hy : y ≠ 0) :
    SameRay R (x + y) z ↔ SameRay R y z := by
  have hxy : SameRay R (x + y) y := h.add_left SameRay.rfl
  exact ⟨fun h' ↦ hxy.symm.trans_of_ne_zero h' (add_comm x y ▸ h.symm.add_ne_zero hy),
    fun h' ↦ hxy.trans_of_ne_zero h' hy⟩
