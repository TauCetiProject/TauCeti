/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Graded.TotalHom

/-!
# Graded linear quivers induced along a map of objects

For a graded linear quiver `C` and a map `F : D → C`, the **induced quiver** `InducedQuiver C F`
has an object `X` for each object `X.obj` of `D`, and as morphisms `X ⟶ Y` the graded hom module
of `C` from `F X.obj` to `F Y.obj`.  It is the graded-quiver analogue of Mathlib's
`CategoryTheory.InducedCategory`, with the objects of `D` wrapped in a structure.  The full
subquiver `TauCeti.GradedLinearQuiver.FullSubquiver P` on the objects satisfying a predicate `P`
is the induced quiver along `Subtype.val`.  An `A∞` structure on `C` induces one on the induced
quiver (`TauCeti.AInfinityCategory.induced`), operating on a composable string as `C` does on its
image.

The total module of morphisms of the induced quiver maps to that of `C`
(`TauCeti.GradedLinearQuiver.InducedQuiver.totalHomMap`), sending a morphism `X ⟶ Y` to the same
morphism `F X.obj ⟶ F Y.obj`.  The map preserves degrees and is injective on each hom module.
Unlike the inclusion of a full subquiver it is not injective when `F` is not, since distinct pairs
of objects can have the same image; nor does it detect composability, since a string of morphisms
that is not composable in the induced quiver can become composable in `C`.

## Main definitions

* `TauCeti.GradedLinearQuiver.InducedQuiver`: the objects of `D`, with the graded hom modules of
  `C` between their images under `F`.
* `TauCeti.GradedLinearQuiver.InducedQuiver.totalHomMap`: the map of total modules of morphisms.

## Main results

* `TauCeti.GradedLinearQuiver.InducedQuiver.totalHomMap_homInclusion`: the map sends a morphism of
  the induced quiver to the same morphism of `C`.
* `TauCeti.GradedLinearQuiver.InducedQuiver.totalHomMap_mem_totalGrading_piece`: the map preserves
  degrees.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 7, for `A∞` categories
  and functors.
-/

public section

open scoped DirectSum

namespace TauCeti.GradedLinearQuiver

universe u u' v w

variable {D : Type u'} (C : Type u)

/-- The objects of the **quiver induced** along `F : D → C`: one object for each object of `D`.
When `C` is a graded linear quiver, so is `InducedQuiver C F`, with the hom module of `C` from
`F X.obj` to `F Y.obj` as its hom module from `X` to `Y`. -/
@[ext]
structure InducedQuiver (F : D → C) where
  /-- The underlying object of `D`. -/
  obj : D

namespace InducedQuiver

variable {R : Type w} [CommRing R] {C} [GradedLinearQuiver.{u, v, w} R C] {F : D → C}

/-- The induced quiver of a graded linear quiver is a graded linear quiver, with the graded hom
modules of `C` between the images of the objects. -/
instance : GradedLinearQuiver.{u', v, w} R (InducedQuiver C F) where
  homModule X Y := homModule (R := R) (F X.obj) (F Y.obj)
  grading X Y := grading (R := R) (F X.obj) (F Y.obj)

/-- The hom module between two objects of an induced quiver is the hom module of `C` between their
images. -/
theorem homModule_eq (X Y : InducedQuiver C F) :
    homModule (R := R) X Y = homModule (R := R) (F X.obj) (F Y.obj) := (rfl)

/-- The grading of the hom module between two objects of an induced quiver is the grading in `C`
between their images. -/
theorem grading_eq (X Y : InducedQuiver C F) :
    grading (R := R) X Y = grading (R := R) (F X.obj) (F Y.obj) := (rfl)

variable (R F) in
/-- The **map of total modules of morphisms** of the induced quiver to that of `C`: on the hom
module of `X` and `Y` it is the inclusion of the hom module of `F X.obj` and `F Y.obj`. -/
noncomputable def totalHomMap : TotalHom R (InducedQuiver C F) →ₗ[R] TotalHom R C :=
  letI := Classical.decEq (InducedQuiver C F × InducedQuiver C F)
  DirectSum.toModule R _ _ fun p ↦ homInclusion (R := R) (F p.1.obj) (F p.2.obj)

/-- The map of total modules sends a morphism `X ⟶ Y` of the induced quiver to the same morphism
`F X.obj ⟶ F Y.obj` of `C`. -/
@[simp]
theorem totalHomMap_homInclusion (X Y : InducedQuiver C F) (f : homModule (R := R) X Y) :
    totalHomMap R F (homInclusion X Y f) = homInclusion (R := R) (F X.obj) (F Y.obj) f := by
  classical
  rw [totalHomMap, homInclusion_eq_lof]
  convert DirectSum.toModule_lof R
    (M := fun p : InducedQuiver C F × InducedQuiver C F ↦ homModule (R := R) p.1 p.2) (X, Y) f

/-- The map of total modules of an induced quiver preserves degrees. -/
theorem totalHomMap_mem_totalGrading_piece {n : ℤ} {x : TotalHom R (InducedQuiver C F)}
    (hx : x ∈ (totalGrading R (InducedQuiver C F)).piece n) :
    totalHomMap R F x ∈ (totalGrading R C).piece n := by
  refine totalGrading_piece_induction (P := fun x ↦ totalHomMap R F x ∈ _) ?_ ?_ ?_ hx
  · simp
  · intro x y hx hy
    simpa using add_mem hx hy
  · intro X Y f hf
    rwa [totalHomMap_homInclusion, homInclusion_mem_totalGrading_piece_iff]

end InducedQuiver

end TauCeti.GradedLinearQuiver
