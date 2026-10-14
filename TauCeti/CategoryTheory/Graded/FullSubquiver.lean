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

Since `Subtype.val` is injective, this map of total modules is injective and detects degrees, as
recorded here.  Moreover a string of morphisms which is not composable in the full subquiver is
sent to a string which is not composable in `C`, since distinct objects of the full subquiver are
distinct objects of `C`.

## Main definitions

* `TauCeti.GradedLinearQuiver.FullSubquiver`: the objects of `C` satisfying a predicate, with the
  graded hom modules of `C`.

## Main results

* `TauCeti.GradedLinearQuiver.FullSubquiver.homProjection_totalHomMap`: the components of the
  image of an element in the total module of `C`.
* `TauCeti.GradedLinearQuiver.FullSubquiver.totalHomMap_injective` and
  `TauCeti.GradedLinearQuiver.FullSubquiver.totalHomMap_mem_totalGrading_piece_iff`: the map of
  total modules is injective and detects degrees.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 7, for `A∞` categories.
  A full subcategory keeps the morphisms between the chosen objects and the operations on them.
-/

public section

open scoped DirectSum

namespace TauCeti.GradedLinearQuiver

universe u v w

variable {C : Type u}

/-- The objects of the **full subquiver** of `C` on the objects satisfying `P`: the induced quiver
along the inclusion of the objects satisfying `P`.  When `C` is a graded linear quiver, so is the
full subquiver, with the hom modules of `C`. -/
abbrev FullSubquiver (P : C → Prop) : Type u :=
  InducedQuiver C (Subtype.val : Subtype P → C)

namespace FullSubquiver

open InducedQuiver

variable {R : Type w} [CommRing R] [GradedLinearQuiver.{u, v, w} R C] {P : C → Prop}

/-- The component, between objects of the full subquiver, of the image of an element in the total
module of `C` is its component in the full subquiver. -/
@[simp]
theorem homProjection_totalHomMap (X Y : FullSubquiver P)
    (x : TotalHom R (FullSubquiver P)) :
    homProjection (R := R) (X.obj : C) Y.obj (totalHomMap R Subtype.val x) =
      homProjection X Y x := by
  classical
  suffices h : homProjection (R := R) (X.obj : C) Y.obj ∘ₗ totalHomMap R Subtype.val =
      homProjection (R := R) (C := FullSubquiver P) X Y from LinearMap.congr_fun h x
  refine DirectSum.linearMap_ext R fun p ↦ LinearMap.ext fun f ↦ ?_
  simp only [LinearMap.comp_apply, ← homInclusion_eq_lof p.1 p.2, totalHomMap_homInclusion]
  by_cases h : p = (X, Y)
  · subst h
    rw [homProjection_homInclusion, homProjection_homInclusion]
  · have h' : ((p.1.obj : C), (p.2.obj : C)) ≠ ((X.obj : C), (Y.obj : C)) := fun e ↦ h <|
      Prod.ext (InducedQuiver.ext (Subtype.ext (congrArg Prod.fst e)))
        (InducedQuiver.ext (Subtype.ext (congrArg Prod.snd e)))
    rw [homProjection_homInclusion_of_ne h, homProjection_homInclusion_of_ne h']

/-- The component of the image of an element between two objects of `C` not both in the full
subquiver vanishes. -/
@[simp]
theorem homProjection_totalHomMap_of_not {X Y : C} (h : ¬ (P X ∧ P Y))
    (x : TotalHom R (FullSubquiver P)) :
    homProjection (R := R) X Y (totalHomMap R Subtype.val x) = 0 := by
  classical
  suffices e : homProjection (R := R) X Y ∘ₗ totalHomMap R (Subtype.val : Subtype P → C) = 0 from
    LinearMap.congr_fun e x
  refine DirectSum.linearMap_ext R fun p ↦ LinearMap.ext fun f ↦ ?_
  simp only [LinearMap.comp_apply, ← homInclusion_eq_lof p.1 p.2, totalHomMap_homInclusion,
    LinearMap.zero_apply]
  refine homProjection_homInclusion_of_ne (X := (p.1.obj : C)) (Y := (p.2.obj : C))
    (fun e ↦ h ?_) f
  obtain ⟨e₁, e₂⟩ := Prod.mk.inj e
  exact ⟨e₁ ▸ p.1.obj.property, e₂ ▸ p.2.obj.property⟩

/-- The map of total modules of morphisms of a full subquiver is injective. -/
theorem totalHomMap_injective :
    Function.Injective (totalHomMap R (Subtype.val : Subtype P → C)) := fun x y h ↦
  totalHom_ext fun X Y ↦ by
    rw [← homProjection_totalHomMap, h, homProjection_totalHomMap]

/-- The map of total modules of morphisms of a full subquiver detects degrees. -/
@[simp]
theorem totalHomMap_mem_totalGrading_piece_iff (n : ℤ) (x : TotalHom R (FullSubquiver P)) :
    totalHomMap R Subtype.val x ∈ (totalGrading R C).piece n ↔
      x ∈ (totalGrading R (FullSubquiver P)).piece n := by
  rw [mem_totalGrading_piece_iff, mem_totalGrading_piece_iff]
  refine ⟨fun h X Y ↦ (homProjection_totalHomMap X Y x) ▸ h X.obj Y.obj, fun h X Y ↦ ?_⟩
  by_cases hXY : P X ∧ P Y
  · convert h ⟨⟨X, hXY.1⟩⟩ ⟨⟨Y, hXY.2⟩⟩ using 1
    exact homProjection_totalHomMap ⟨⟨X, hXY.1⟩⟩ ⟨⟨Y, hXY.2⟩⟩ x
  · rw [homProjection_totalHomMap_of_not hXY]
    exact zero_mem _

end FullSubquiver

end TauCeti.GradedLinearQuiver
