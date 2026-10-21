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
When `F` is injective, the map is injective and detects degrees.  When `F` is not injective, the
map need not be injective, since distinct pairs of objects can have the same image and hence the
same hom module of `C`; and a string of morphisms that is not composable in the induced quiver can
become composable in `C`.

## Main definitions

* `TauCeti.GradedLinearQuiver.InducedQuiver`: the objects of `D`, with the graded hom modules of
  `C` between their images under `F`.
* `TauCeti.GradedLinearQuiver.InducedQuiver.totalHomMap`: the map of total modules of morphisms.

## Main results

* `TauCeti.GradedLinearQuiver.InducedQuiver.totalHomMap_homInclusion`: the map sends a morphism of
  the induced quiver to the same morphism of `C`.
* `TauCeti.GradedLinearQuiver.InducedQuiver.totalHomMap_mem_totalGrading_piece`: the map preserves
  degrees.
* `TauCeti.GradedLinearQuiver.InducedQuiver.totalHomMap_injective` and
  `TauCeti.GradedLinearQuiver.InducedQuiver.totalHomMap_mem_totalGrading_piece_iff`: along an
  injective map of objects, the map is injective and detects degrees.

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

/-- The map of total modules of an induced quiver is homogeneous of degree zero. -/
theorem isHomogeneous_totalHomMap :
    LinearMap.IsHomogeneous (totalHomMap R F) (totalGrading R (InducedQuiver C F)).piece
      (totalGrading R C).piece 0 := by
  rw [LinearMap.isHomogeneous_def]
  intro p x hx
  rw [add_zero]
  exact totalHomMap_mem_totalGrading_piece hx

/-- The map of total modules of an induced quiver commutes with the Koszul twists. -/
theorem koszulTwist_totalHomMap (q : ℤ) (x : TotalHom R (InducedQuiver C F)) :
    (totalGrading R C).koszulTwist q (totalHomMap R F x) =
      totalHomMap R F ((totalGrading R (InducedQuiver C F)).koszulTwist q x) := by
  simpa using LinearMap.congr_fun (isHomogeneous_totalHomMap.koszulTwist_comp q) x

/-- The component of the image of an element between two objects of `C` not both in the image of
`F` vanishes. -/
theorem homProjection_totalHomMap_of_not {X Y : C} (h : ¬ (X ∈ Set.range F ∧ Y ∈ Set.range F))
    (x : TotalHom R (InducedQuiver C F)) :
    homProjection (R := R) X Y (totalHomMap R F x) = 0 := by
  classical
  suffices e : homProjection (R := R) X Y ∘ₗ totalHomMap R F = 0 from LinearMap.congr_fun e x
  refine DirectSum.linearMap_ext R fun p ↦ LinearMap.ext fun f ↦ ?_
  simp only [LinearMap.comp_apply, ← homInclusion_eq_lof p.1 p.2, totalHomMap_homInclusion,
    LinearMap.zero_apply]
  refine homProjection_homInclusion_of_ne (X := F p.1.obj) (Y := F p.2.obj) (fun e ↦ h ?_) f
  obtain ⟨e₁, e₂⟩ := Prod.mk.inj e
  exact ⟨⟨p.1.obj, e₁⟩, ⟨p.2.obj, e₂⟩⟩

section Injective

variable (hF : Function.Injective F)
include hF

/-- Along an injective map of objects, the component between the images of two objects of the
image of an element in the total module of `C` is its component in the induced quiver. -/
@[simp]
theorem homProjection_totalHomMap (X Y : InducedQuiver C F)
    (x : TotalHom R (InducedQuiver C F)) :
    homProjection (R := R) (F X.obj) (F Y.obj) (totalHomMap R F x) = homProjection X Y x := by
  classical
  suffices h : homProjection (R := R) (F X.obj) (F Y.obj) ∘ₗ totalHomMap R F =
      homProjection (R := R) (C := InducedQuiver C F) X Y from LinearMap.congr_fun h x
  refine DirectSum.linearMap_ext R fun p ↦ LinearMap.ext fun f ↦ ?_
  simp only [LinearMap.comp_apply, ← homInclusion_eq_lof p.1 p.2, totalHomMap_homInclusion]
  by_cases h : p = (X, Y)
  · subst h
    rw [homProjection_homInclusion, homProjection_homInclusion]
  · have h' : (F p.1.obj, F p.2.obj) ≠ (F X.obj, F Y.obj) := fun e ↦ h <|
      Prod.ext (InducedQuiver.ext (hF (congrArg Prod.fst e)))
        (InducedQuiver.ext (hF (congrArg Prod.snd e)))
    rw [homProjection_homInclusion_of_ne h, homProjection_homInclusion_of_ne h']

/-- Along an injective map of objects, the map of total modules of morphisms is injective. -/
theorem totalHomMap_injective : Function.Injective (totalHomMap R F) := fun x y h ↦
  totalHom_ext fun X Y ↦ by
    rw [← homProjection_totalHomMap hF, h, homProjection_totalHomMap hF]

/-- Along an injective map of objects, the map of total modules of morphisms detects degrees. -/
theorem totalHomMap_mem_totalGrading_piece_iff (n : ℤ) (x : TotalHom R (InducedQuiver C F)) :
    totalHomMap R F x ∈ (totalGrading R C).piece n ↔
      x ∈ (totalGrading R (InducedQuiver C F)).piece n := by
  rw [mem_totalGrading_piece_iff, mem_totalGrading_piece_iff]
  refine ⟨fun h X Y ↦ homProjection_totalHomMap hF X Y x ▸ h (F X.obj) (F Y.obj),
    fun h X Y ↦ ?_⟩
  by_cases hXY : X ∈ Set.range F ∧ Y ∈ Set.range F
  · obtain ⟨⟨X, rfl⟩, ⟨Y, rfl⟩⟩ := hXY
    rw [homProjection_totalHomMap hF ⟨X⟩ ⟨Y⟩]
    exact h ⟨X⟩ ⟨Y⟩
  · rw [homProjection_totalHomMap_of_not hXY]
    exact zero_mem _

end Injective

end InducedQuiver

end TauCeti.GradedLinearQuiver
