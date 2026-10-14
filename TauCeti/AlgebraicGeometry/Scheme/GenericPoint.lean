/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Stalk

import TauCeti.Topology.KrullDimension.Basic

/-!
# The generic point of an irreducible scheme and the specialization order

The points of a scheme are ordered by specialization: `x ≤ y` when `y` generizes `x`. On an
irreducible scheme the generic point generizes every point, so it is maximal for this order, and
it is the only maximal point: a point with no proper generization is generized by the generic
point and generizes it, hence equals it because the underlying space of a scheme is T₀. Since the
points of coheight zero are the maximal ones, this identifies the points of coheight zero of an
irreducible scheme with its generic point. On an irreducible scheme of dimension at most one,
every other point then has codimension exactly one.

On an integral scheme `X`, the morphism `Spec k(X) ⟶ X` from the spectrum of the function field
to the generic point is quasi-compact, since `Spec k(X)` is a single point.

## Main results

* `TauCeti.AlgebraicGeometry.Scheme.isMax_genericPoint`: the generic point of an irreducible
  scheme is maximal for the specialization order;
* `TauCeti.AlgebraicGeometry.Scheme.eq_genericPoint_of_isMax`: a point of an irreducible scheme
  which is maximal for the specialization order is the generic point;
* `TauCeti.AlgebraicGeometry.Scheme.isMax_iff_eq_genericPoint`: the maximal points for the
  specialization order on an irreducible scheme are exactly the generic point;
* `TauCeti.AlgebraicGeometry.Scheme.coheight_eq_one_iff_ne_genericPoint`: on an irreducible
  scheme of dimension at most one, the points of codimension one are exactly the points other
  than the generic point.
* `TauCeti.AlgebraicGeometry.Scheme.quasiCompact_fromSpecStalk_genericPoint`: the generic point
  `Spec k(X) ⟶ X` of an integral scheme is quasi-compact.
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

/-- On an irreducible scheme of dimension at most one, the points of codimension one are exactly
the points other than the generic point. -/
theorem coheight_eq_one_iff_ne_genericPoint
    (hX : topologicalKrullDim X ≤ 1) {y : X} : Order.coheight y = 1 ↔ y ≠ genericPoint X := by
  have hle : Order.coheight y ≤ 1 := by
    exact_mod_cast (TauCeti.coheight_le_topologicalKrullDim y).trans hX
  rw [← hle.ge_iff_eq, Order.one_le_iff_pos, Order.coheight_pos, not_iff_not,
    isMax_iff_eq_genericPoint]

/-- The generic point `Spec k(X) ⟶ X` of an integral scheme is quasi-compact, since `Spec k(X)` is
a single point. -/
instance quasiCompact_fromSpecStalk_genericPoint {X : Scheme.{u}} [IsIntegral X] :
    QuasiCompact (X.fromSpecStalk (genericPoint X)) :=
  have : Finite (Spec X.functionField) := inferInstanceAs (Finite (PrimeSpectrum X.functionField))
  ⟨fun _ _ _ ↦ (Set.toFinite _).isCompact⟩

end Scheme

end AlgebraicGeometry

end TauCeti
