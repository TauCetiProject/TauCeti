/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Convex.Cone.Face.Basic

/-!
# Elementary faces of pointed cones

Mathlib's `ConvexCone.Salient` records that a convex cone contains no line. This file
characterises salience through the face lattice of a pointed cone: when scalar multiplication has
no zero divisors, the zero cone is a face exactly when the cone is salient. It also records that a
face of a cone cuts out a face of every smaller cone.

## Main declarations

* `PointedCone.bot_isFaceOf_iff`: the zero cone is a face of a pointed cone if and only if the
  cone is salient.
* `PointedCone.IsFaceOf.salient_of_bot`: a pointed cone having the zero cone as a face is salient;
  this direction needs no hypothesis on scalar multiplication.
* `ConvexCone.Salient.bot_isFaceOf`: the zero cone is a face of a salient pointed cone.
* `PointedCone.IsFaceOf.inf_of_le`: a face of a cone meets a smaller cone in a face of the
  smaller cone.
-/

public section

variable {R V : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup V]
  [Module R V] {C : PointedCone R V}

namespace PointedCone.IsFaceOf

variable {F τ : PointedCone R V}

/-- A face `F` of a cone `τ` meets a cone `C ≤ τ` in a face of `C`. -/
theorem inf_of_le (hF : F.IsFaceOf τ) (hC : C ≤ τ) : (C ⊓ F).IsFaceOf C := by
  simpa [inf_eq_left.2 hC] using (PointedCone.IsFaceOf.refl C).inf hF

/-- A pointed cone having the zero cone as a face is salient. -/
theorem salient_of_bot (h : (⊥ : PointedCone R V).IsFaceOf C) :
    (C : ConvexCone R V).Salient := by
  intro x hx hx0 hnx
  -- `x + -x = 0` lies in the face `⊥`, so `x` does too.
  exact hx0 <| (Submodule.mem_bot R).1 <| h.mem_of_add_mem_left hx hnx (by simp)

end PointedCone.IsFaceOf

variable [NoZeroSMulDivisors R V]

/-- The zero cone is a face of a salient pointed cone. -/
theorem ConvexCone.Salient.bot_isFaceOf (hC : (C : ConvexCone R V).Salient) :
    (⊥ : PointedCone R V).IsFaceOf C := by
  refine ⟨bot_le, fun {x y a} hx hy ha hxy ↦ ?_⟩
  rw [Submodule.mem_bot] at hxy ⊢
  rw [eq_neg_of_add_eq_zero_right hxy] at hy
  -- A nonzero positive multiple of `x` whose negative is `y ∈ C` would be a line in `C`.
  have hzero : a • x = 0 := by
    by_contra h
    exact hC _ (C.smul_mem ha.le hx) h hy
  exact (eq_zero_or_eq_zero_of_smul_eq_zero hzero).resolve_left ha.ne'

/-- The zero cone is a face of a pointed cone if and only if the cone is salient. -/
theorem PointedCone.bot_isFaceOf_iff :
    (⊥ : PointedCone R V).IsFaceOf C ↔ (C : ConvexCone R V).Salient :=
  ⟨IsFaceOf.salient_of_bot, ConvexCone.Salient.bot_isFaceOf⟩
