/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.AInfinity.Induced
public import TauCeti.CategoryTheory.Graded.FullSubquiver

/-!
# Full subcategories of A-infinity categories

Restricting the objects of an `A∞` category `𝒞` on a graded linear quiver `C` to those satisfying
a predicate `P` leaves its hom modules and its operations on composable strings intact.  This is
the **full subcategory** `𝒞.fullSubcategory P`, the `A∞` category induced along the inclusion
`Subtype.val` of the objects satisfying `P` (`TauCeti.AInfinityCategory.induced`), on the full
subquiver `TauCeti.GradedLinearQuiver.FullSubquiver P`.  It is reducible, so the API of induced
categories (operations on composable strings, differential, composition) applies to it directly.

Since `Subtype.val` is injective, the map of total modules of morphisms of the full subquiver into
that of `C` intertwines the operations on all strings, not only on composable ones: a string of
morphisms which is not composable in the full subquiver is not composable in `C`.  It is therefore
a strict `A∞` morphism of total algebras, `𝒞.inducedInclusion Subtype.val_injective`
(`TauCeti.AInfinityCategory.inducedInclusion`).
The homotopy-level consequences are in
`TauCeti.CategoryTheory.AInfinity.FullSubcategory.HomotopyCategory`.

## Main definitions

* `TauCeti.AInfinityCategory.fullSubcategory`: the full `A∞` subcategory on the objects
  satisfying a predicate.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 7, for `A∞` categories.
  A full subcategory keeps the morphisms between the chosen objects and the operations on them.
-/

public section

namespace TauCeti

universe u v w

open GradedLinearQuiver

namespace AInfinityCategory

variable {R : Type w} [CommRing R] {C : Type u} [GradedLinearQuiver.{u, v, w} R C]
  (𝒞 : AInfinityCategory R C) (P : C → Prop)

/-- The **full subcategory** of an `A∞` category on the objects satisfying `P`: the `A∞` category
induced along the inclusion of these objects, whose operations on composable strings are those of
`𝒞`. -/
noncomputable abbrev fullSubcategory : AInfinityCategory R (FullSubquiver P) :=
  𝒞.induced Subtype.val

end AInfinityCategory

end TauCeti
