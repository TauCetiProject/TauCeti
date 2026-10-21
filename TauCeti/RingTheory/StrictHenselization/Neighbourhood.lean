/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.RingTheory.Etale.Basic

/-!
# Pointed étale neighbourhoods

Étale algebras with a map to a fixed commutative algebra form the indexing category for strict
henselization.

For `R : Type u` and `Ω : Type v`, source algebras live in `Type (max u v)`.
The target is lifted to this universe, so the base algebra and tensor-product refinements belong
to the same category even when the base and target have different universes.

## References

* Stacks Project, Tag 04GW.
* Taylor Dupuy, Thomas Tucker, and Zhuoran Wang, pcfawd-formalization at `9a20b3f`,
  `StrictHenselizationConstruction.lean`, `PointedEtaleNeighborhood`.
-/

public section

open CategoryTheory

universe u v

namespace TauCeti.StrictHenselization

variable (R : Type u) (Ω : Type v) [CommRing R] [CommRing Ω] [Algebra R Ω]

/-- An étale algebra equipped with a point valued in the universe lift of `Ω`. -/
def IsPointedNeighbourhood : ObjectProperty (Over (CommAlgCat.of R (ULift.{u} Ω))) :=
  fun point ↦ Algebra.Etale R point.left

/-- The category of pointed étale neighbourhoods. -/
abbrev Neighbourhood := (IsPointedNeighbourhood R Ω).FullSubcategory

/-- The defining property of a pointed neighbourhood. -/
@[simp]
theorem isPointedNeighbourhood_iff (point : Over (CommAlgCat.of R (ULift.{u} Ω))) :
    IsPointedNeighbourhood R Ω point ↔ Algebra.Etale R point.left :=
  Iff.rfl

/-- Pointed neighbourhoods agree when their source algebras and point maps agree. -/
@[ext]
theorem Neighbourhood.ext (first second : Neighbourhood R Ω)
    (hleft : first.obj.left = second.obj.left)
    (hpoint : HEq first.obj.hom.hom second.obj.hom.hom) : first = second := by
  cases first with
  | mk firstObj firstProperty =>
    cases second with
    | mk secondObj secondProperty =>
      cases firstObj with
      | mk firstLeft firstRight firstHom =>
        cases secondObj with
        | mk secondLeft secondRight secondHom =>
          have hright : firstRight = secondRight := Subsingleton.elim _ _
          cases hright
          cases hleft
          have hmap : firstHom.hom = secondHom.hom := eq_of_heq hpoint
          have hhom : firstHom = secondHom := CommAlgCat.hom_ext hmap
          cases hhom
          rfl

end TauCeti.StrictHenselization
