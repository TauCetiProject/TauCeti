/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Graded.InducedQuiver

/-!
# Full subquivers of graded linear quivers

The **full subquiver** of a graded linear quiver `C` on the objects satisfying a predicate `P` has
those objects, and between two of them the graded hom module of `C`.  It is the induced quiver
`TauCeti.GradedLinearQuiver.InducedQuiver` along the inclusion `Subtype.val` of the objects
satisfying `P`, as Mathlib builds full subcategories as induced categories, so its graded linear
quiver structure and its map of total modules of morphisms
`TauCeti.GradedLinearQuiver.InducedQuiver.totalHomMap` are those of the induced quiver.

Since `Subtype.val` is injective, the results on induced quivers along injective maps apply:
the map of total modules is injective and detects degrees
(`TauCeti.GradedLinearQuiver.InducedQuiver.totalHomMap_injective` and
`TauCeti.GradedLinearQuiver.InducedQuiver.totalHomMap_mem_totalGrading_piece_iff` with
`Subtype.val_injective`).

## Main definitions

* `TauCeti.GradedLinearQuiver.FullSubquiver`: the objects of `C` satisfying a predicate, with the
  graded hom modules of `C`.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 7, for `A∞` categories.
  A full subcategory keeps the morphisms between the chosen objects and the operations on them.
-/

public section

namespace TauCeti.GradedLinearQuiver

universe u

variable {C : Type u}

/-- The objects of the **full subquiver** of `C` on the objects satisfying `P`: the induced quiver
along the inclusion of the objects satisfying `P`.  When `C` is a graded linear quiver, so is the
full subquiver, with the hom modules of `C`. -/
abbrev FullSubquiver (P : C → Prop) : Type u :=
  InducedQuiver C (Subtype.val : Subtype P → C)

end TauCeti.GradedLinearQuiver
