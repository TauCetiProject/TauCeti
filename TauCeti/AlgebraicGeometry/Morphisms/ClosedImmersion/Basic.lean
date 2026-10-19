/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Factoring morphisms over a base through closed immersions

Mathlib's `IsClosedImmersion.lift` factors a scheme morphism through a closed immersion
when the defining ideal vanishes on the source. The factor remains over the same base.
This file packages that lift in `Over S`, for use with structure maps of group schemes.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

universe u

variable {S : Scheme.{u}} {X Y Z : Over S}

/-- Factor a morphism over `S` through a closed immersion over `S`, when the defining ideal
of the immersion vanishes on the morphism. -/
noncomputable def closedImmersionOverLift (i : X ⟶ Y) (f : Z ⟶ Y)
    [IsClosedImmersion i.left] (h : i.left.ker ≤ f.left.ker) : Z ⟶ X :=
  Over.homMk (IsClosedImmersion.lift i.left f.left h) (by
    rw [← i.w, ← Category.assoc, IsClosedImmersion.lift_fac, f.w])

/-- The underlying scheme morphism of the lift is Mathlib's closed-immersion lift. -/
@[simp]
theorem closedImmersionOverLift_left (i : X ⟶ Y) (f : Z ⟶ Y)
    [IsClosedImmersion i.left] (h : i.left.ker ≤ f.left.ker) :
    (closedImmersionOverLift i f h).left = IsClosedImmersion.lift i.left f.left h := (rfl)

/-- The lift factors the original morphism over the base. -/
@[reassoc (attr := simp)]
theorem closedImmersionOverLift_comp (i : X ⟶ Y) (f : Z ⟶ Y)
    [IsClosedImmersion i.left] (h : i.left.ker ≤ f.left.ker) :
    closedImmersionOverLift i f h ≫ i = f := by
  ext
  simp

end TauCeti
