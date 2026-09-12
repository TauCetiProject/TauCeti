/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Convex.Cone.Face.Basic

/-!
# The zero face of a salient cone

Mathlib's `ConvexCone.Salient` records that a convex cone contains no line. This file records the
consequence of salience for the face lattice of a pointed cone: the zero cone is a face.

## Main declarations

* `ConvexCone.Salient.bot_isFaceOf`: the zero cone is a face of a salient pointed cone.
-/

public section

namespace ConvexCone.Salient

variable {R V : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup V]
  [Module R V] [NoZeroSMulDivisors R V] {C : PointedCone R V}

/-- The zero cone is a face of a salient pointed cone. -/
theorem bot_isFaceOf (hC : (C : ConvexCone R V).Salient) :
    (⊥ : PointedCone R V).IsFaceOf C := by
  refine ⟨bot_le, fun {x y a} hx hy ha hxy ↦ ?_⟩
  rw [Submodule.mem_bot] at hxy ⊢
  rw [eq_neg_of_add_eq_zero_right hxy] at hy
  -- A nonzero positive multiple of `x` whose negative is `y ∈ C` would be a line in `C`.
  have hzero : a • x = 0 := by
    by_contra h
    exact hC _ (C.smul_mem ha.le hx) h hy
  exact (eq_zero_or_eq_zero_of_smul_eq_zero hzero).resolve_left ha.ne'

end ConvexCone.Salient
