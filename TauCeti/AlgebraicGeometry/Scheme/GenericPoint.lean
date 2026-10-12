/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Properties

/-!
# The generic point of an irreducible scheme and the specialization order

The points of a scheme are ordered by specialization: `x ≤ y` when `y` generizes `x`. On an
irreducible scheme the generic point generizes every point, so it is maximal for this order, and
it is the only maximal point: a point with no proper generization is generized by the generic
point and generizes it, hence equals it because the underlying space of a scheme is T₀. Since the
points of coheight zero are the maximal ones, this identifies the points of coheight zero of an
irreducible scheme with its generic point.

## Main results

* `TauCeti.AlgebraicGeometry.Scheme.isMax_genericPoint`: the generic point of an irreducible
  scheme is maximal for the specialization order;
* `TauCeti.AlgebraicGeometry.Scheme.eq_genericPoint_of_isMax`: a point of an irreducible scheme
  which is maximal for the specialization order is the generic point;
* `TauCeti.AlgebraicGeometry.Scheme.isMax_iff_eq_genericPoint`: the maximal points for the
  specialization order on an irreducible scheme are exactly the generic point.
-/

public section

open AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

namespace Scheme

universe u

variable {X : Scheme.{u}} [IrreducibleSpace X]

/-- The generic point of an irreducible scheme is maximal for the specialization order: it
generizes every point. -/
theorem isMax_genericPoint : IsMax (genericPoint X) := fun y _ ↦ genericPoint_specializes y

/-- A point of an irreducible scheme which is maximal for the specialization order, that is, a
point of coheight zero, is the generic point. -/
theorem eq_genericPoint_of_isMax {y : X} (hy : IsMax y) : y = genericPoint X :=
  (Specializes.antisymm (hy (genericPoint_specializes y)) (genericPoint_specializes y)).eq

/-- The points of an irreducible scheme which are maximal for the specialization order are
exactly the generic point. -/
theorem isMax_iff_eq_genericPoint {y : X} : IsMax y ↔ y = genericPoint X :=
  ⟨eq_genericPoint_of_isMax, fun h ↦ h ▸ isMax_genericPoint⟩

end Scheme

end AlgebraicGeometry

end TauCeti
