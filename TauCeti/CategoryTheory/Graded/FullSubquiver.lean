/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Graded.TotalHom

/-!
# Full subquivers of graded linear quivers

The **full subquiver** of a graded linear quiver `C` on the objects satisfying a predicate `P` has
those objects, and between two of them the graded hom module of `C`.  Structure carried by `C`
whose operations send composable strings to morphisms between their endpoints, such as an `A∞`
structure, restricts to it, giving full subcategories.

Its total module of morphisms is the sum of the hom modules of the pairs of objects satisfying `P`,
so it includes into the total module of `C`
(`TauCeti.GradedLinearQuiver.FullSubquiver.totalHomInclusion`).  The inclusion is injective,
detects degrees, and sends a string of morphisms which is not composable in the full subquiver to a
string which is not composable in `C`, since the objects of the full subquiver are objects of `C`.

## Main definitions

* `TauCeti.GradedLinearQuiver.FullSubquiver`: the objects of `C` satisfying a predicate, with the
  graded hom modules of `C`.
* `TauCeti.GradedLinearQuiver.FullSubquiver.totalHomInclusion`: the inclusion of its total module
  of morphisms into that of `C`.

## Main results

* `TauCeti.GradedLinearQuiver.FullSubquiver.totalHomInclusion_homInclusion`: the inclusion sends
  a morphism of the full subquiver to the same morphism of `C`.
* `TauCeti.GradedLinearQuiver.FullSubquiver.homProjection_totalHomInclusion`: the components of
  the inclusion of an element.
* `TauCeti.GradedLinearQuiver.FullSubquiver.totalHomInclusion_injective` and
  `TauCeti.GradedLinearQuiver.FullSubquiver.totalHomInclusion_mem_totalGrading_piece_iff`: the
  inclusion is injective and detects degrees.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 7, for `A∞` categories.
  A full subcategory keeps the morphisms between the chosen objects and the operations on them.
-/

public section

open scoped DirectSum

namespace TauCeti.GradedLinearQuiver

universe u v w

variable {C : Type u}

/-- The objects of the **full subquiver** of `C` on the objects satisfying `P`.  When `C` is a
graded linear quiver, so is the full subquiver, with the hom modules of `C`. -/
@[ext]
structure FullSubquiver (P : C → Prop) where
  /-- The underlying object. -/
  obj : C
  /-- The predicate holds on the object. -/
  property : P obj

namespace FullSubquiver

variable {R : Type w} [CommRing R] [GradedLinearQuiver.{u, v, w} R C] {P : C → Prop}

/-- The full subquiver of a graded linear quiver is a graded linear quiver, with the graded hom
modules of the ambient quiver. -/
instance : GradedLinearQuiver.{u, v, w} R (FullSubquiver P) where
  homModule X Y := homModule (R := R) X.obj Y.obj
  grading X Y := grading (R := R) X.obj Y.obj

/-- The hom module between two objects of a full subquiver is their hom module in `C`. -/
theorem homModule_eq (X Y : FullSubquiver P) :
    homModule (R := R) X Y = homModule (R := R) X.obj Y.obj := (rfl)

/-- The grading of the hom module between two objects of a full subquiver is their grading in
`C`. -/
theorem grading_eq (X Y : FullSubquiver P) :
    grading (R := R) X Y = grading (R := R) X.obj Y.obj := (rfl)

variable (R P) in
/-- The **inclusion of the total module of morphisms** of a full subquiver into that of `C`: the
sum of the inclusions of the hom modules of the pairs of objects of the full subquiver. -/
noncomputable def totalHomInclusion : TotalHom R (FullSubquiver P) →ₗ[R] TotalHom R C :=
  letI := Classical.decEq (FullSubquiver P × FullSubquiver P)
  DirectSum.toModule R _ _ fun p ↦ homInclusion (R := R) p.1.obj p.2.obj

/-- The inclusion of total modules sends a morphism of the full subquiver to the same morphism
of `C`. -/
@[simp]
theorem totalHomInclusion_homInclusion (X Y : FullSubquiver P) (f : homModule (R := R) X Y) :
    totalHomInclusion R P (homInclusion X Y f) = homInclusion (R := R) X.obj Y.obj f := by
  classical
  rw [totalHomInclusion, homInclusion_eq_lof]
  convert DirectSum.toModule_lof R
    (M := fun p : FullSubquiver P × FullSubquiver P ↦ homModule (R := R) p.1 p.2) (X, Y) f

/-- The component, between objects of the full subquiver, of the inclusion of an element is its
component in the full subquiver. -/
@[simp]
theorem homProjection_totalHomInclusion (X Y : FullSubquiver P)
    (x : TotalHom R (FullSubquiver P)) :
    homProjection (R := R) X.obj Y.obj (totalHomInclusion R P x) = homProjection X Y x := by
  classical
  suffices h : homProjection (R := R) X.obj Y.obj ∘ₗ totalHomInclusion R P =
      homProjection (R := R) (C := FullSubquiver P) X Y from LinearMap.congr_fun h x
  refine DirectSum.linearMap_ext R fun p ↦ LinearMap.ext fun f ↦ ?_
  simp only [LinearMap.comp_apply, ← homInclusion_eq_lof p.1 p.2, totalHomInclusion_homInclusion]
  by_cases h : p = (X, Y)
  · subst h
    rw [homProjection_homInclusion, homProjection_homInclusion]
  · have h' : (p.1.obj, p.2.obj) ≠ (X.obj, Y.obj) := fun e ↦ h <|
      Prod.ext (FullSubquiver.ext (congrArg Prod.fst e)) (FullSubquiver.ext (congrArg Prod.snd e))
    rw [homProjection_homInclusion_of_ne h, homProjection_homInclusion_of_ne h']

/-- The component of the inclusion of an element between two objects of `C` not both in the full
subquiver vanishes. -/
@[simp]
theorem homProjection_totalHomInclusion_of_not {X Y : C} (h : ¬ (P X ∧ P Y))
    (x : TotalHom R (FullSubquiver P)) :
    homProjection (R := R) X Y (totalHomInclusion R P x) = 0 := by
  classical
  suffices e : homProjection (R := R) X Y ∘ₗ totalHomInclusion R P = 0 from
    LinearMap.congr_fun e x
  refine DirectSum.linearMap_ext R fun p ↦ LinearMap.ext fun f ↦ ?_
  simp only [LinearMap.comp_apply, ← homInclusion_eq_lof p.1 p.2, totalHomInclusion_homInclusion,
    LinearMap.zero_apply]
  refine homProjection_homInclusion_of_ne (X := p.1.obj) (Y := p.2.obj) (fun e ↦ h ?_) f
  obtain ⟨e₁, e₂⟩ := Prod.mk.inj e
  exact ⟨e₁ ▸ p.1.property, e₂ ▸ p.2.property⟩

/-- The inclusion of the total module of morphisms of a full subquiver is injective. -/
theorem totalHomInclusion_injective : Function.Injective (totalHomInclusion R P) := fun x y h ↦
  totalHom_ext fun X Y ↦ by
    rw [← homProjection_totalHomInclusion, h, homProjection_totalHomInclusion]

/-- The inclusion of the total module of morphisms of a full subquiver detects degrees. -/
@[simp]
theorem totalHomInclusion_mem_totalGrading_piece_iff (n : ℤ) (x : TotalHom R (FullSubquiver P)) :
    totalHomInclusion R P x ∈ (totalGrading R C).piece n ↔
      x ∈ (totalGrading R (FullSubquiver P)).piece n := by
  rw [mem_totalGrading_piece_iff, mem_totalGrading_piece_iff]
  refine ⟨fun h X Y ↦ (homProjection_totalHomInclusion X Y x) ▸ h X.obj Y.obj, fun h X Y ↦ ?_⟩
  by_cases hXY : P X ∧ P Y
  · convert h ⟨X, hXY.1⟩ ⟨Y, hXY.2⟩ using 1
    exact homProjection_totalHomInclusion ⟨X, hXY.1⟩ ⟨Y, hXY.2⟩ x
  · rw [homProjection_totalHomInclusion_of_not hXY]
    exact zero_mem _

end FullSubquiver

end TauCeti.GradedLinearQuiver
