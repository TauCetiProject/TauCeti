/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Order.KrullDimension

/-!
# Codimension-one points of a scheme

A point of a scheme has codimension one when its coheight for the specialization order is one,
equivalently when it is the generic point of an irreducible closed subset of codimension one.
This file introduces the subtype of such points and records the one order-theoretic fact about
them that does not mention any further structure: a codimension-one point has no codimension-one
generization other than itself.

The type is used both by the divisor layer, where a codimension-one point represents a prime
divisor, and by the place layer, where it is the centre of a function-field place; it is defined
here so that neither layer has to depend on the other.

## Main declarations

* `TauCeti.AlgebraicGeometry.CodimensionOnePoint`: the codimension-one points of a scheme.
* `TauCeti.AlgebraicGeometry.CodimensionOnePoint.eq_of_specializes`: a codimension-one
  generization of a codimension-one point is equal to it.
-/

public section

open Order AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

/-- A codimension-one point of a scheme. Such a point is the generic point of a prime divisor. -/
abbrev CodimensionOnePoint (X : Scheme.{u}) : Type u :=
  {x : X // coheight x = 1}

/-- A codimension-one point admits no codimension-one generization other than itself: a strict
generization has strictly smaller coheight, and both points have coheight one. -/
lemma CodimensionOnePoint.eq_of_specializes {X : Scheme.{u}} {x y : CodimensionOnePoint X}
    (h : (y : X) ⤳ (x : X)) : y = x := by
  by_contra hne
  have hne' : (x : X) ≠ (y : X) := fun hxy ↦ hne (Subtype.ext hxy.symm)
  have hlt : (x : X) < (y : X) :=
    ⟨h, fun hxy ↦ hne' (Inseparable.eq (inseparable_iff_specializes_and.mpr ⟨hxy, h⟩))⟩
  have hy := Order.coheight_strictAnti hlt (by simp [y.property])
  rw [x.property, y.property] at hy
  exact absurd hy (lt_irrefl 1)

end AlgebraicGeometry

end TauCeti
