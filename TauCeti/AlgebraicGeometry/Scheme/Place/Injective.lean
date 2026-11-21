/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Scheme.CodimensionOnePoint
public import TauCeti.AlgebraicGeometry.Scheme.Place.Basic

import TauCeti.AlgebraicGeometry.Scheme.GenericPoint

/-!
# A place determines its center on a separated scheme

On an integral separated scheme over a field, two points with discrete valuation ring stalks
have the same associated function-field place exactly when they coincide. Equality of the
places identifies their valuation rings inside the function field. Separatedness then identifies
the two maps from the spectrum of this ring to the scheme, and hence their closed-point images.

In particular the map sending a codimension-one point to its place is injective
(`CodimensionOnePoint.toPlace_injective`). This is the injectivity step in comparing the points
of a nonsingular proper curve with the places of its function field, needed to compare divisor
and principal-parts constructions.

## References

* The Stacks Project, Lemma 26.22.1 (Tag 01KZ), uniqueness in the valuative criterion.
* R. Hartshorne, *Algebraic Geometry*, Chapter I, Section 6.
-/

public section

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (.of k))] [X.IsSeparated]

/-- On a separated integral scheme, a function-field place has at most one center whose local
ring is a discrete valuation ring. -/
@[simp]
theorem toPlace_eq_iff {x y : X}
    [IsDiscreteValuationRing (X.presheaf.stalk x)]
    [IsDiscreteValuationRing (X.presheaf.stalk y)] :
    X.toPlace (k := k) x = X.toPlace (k := k) y ↔ x = y := by
  constructor
  · intro h
    obtain ⟨e, he⟩ := X.exists_stalkRingEquiv_of_toPlace_eq h
    have : IsLocalHom e.toRingHom := isLocalHom_of_leftInverse e.symm.toRingHom e.left_inv
    exact Scheme.eq_of_fromSpecStalk_eq_specMap_comp e.toRingHom
      (Scheme.fromSpecStalk_eq_specMap_comp_fromSpecStalk e.toRingHom he)
  · rintro rfl
    rfl

/-- Distinct codimension-one points of a separated integral scheme give distinct function-field
places, provided their local rings are discrete valuation rings. -/
theorem CodimensionOnePoint.toPlace_injective
    [∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X))] :
    Function.Injective (fun x : CodimensionOnePoint X ↦ X.toPlace (k := k) (x : X)) := by
  intro x y h
  exact Subtype.ext (toPlace_eq_iff.mp h)

end TauCeti.AlgebraicGeometry
