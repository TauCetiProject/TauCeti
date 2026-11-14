/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Slices as costructured arrows along a fully faithful functor

For a fully faithful functor `F : C ⥤ D` and an object `X` of `C`, the slice category `Over X` is
equivalent to the category `CostructuredArrow F (F.obj X)` of costructured arrows from `F` to
`F.obj X`, via `f ↦ F.map f`. It is the composite of Mathlib's `CostructuredArrow.post` and
`CostructuredArrow.pre`, both equivalences when `F` is fully faithful.

## Main definitions

* `CategoryTheory.Functor.FullyFaithful.overEquivCostructuredArrow hF X`: for a fully faithful
  functor `F`, the equivalence between `Over X` and `CostructuredArrow F (F.obj X)`.
-/

public section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- For a fully faithful functor `F : C ⥤ D`, the slice category `Over X` is equivalent to the
category of costructured arrows from `F` to `F.obj X`, sending `f : Y ⟶ X` to `F.map f`. -/
@[expose]
noncomputable def Functor.FullyFaithful.overEquivCostructuredArrow {D : Type*} [Category D]
    {F : C ⥤ D} (hF : F.FullyFaithful) (X : C) :
    Over X ≌ CostructuredArrow F (F.obj X) :=
  have := hF.full
  have := hF.faithful
  (CostructuredArrow.post (𝟭 C) F X).asEquivalence.trans
    (CostructuredArrow.pre (𝟭 C) F (F.obj X)).asEquivalence

@[simp]
lemma Functor.FullyFaithful.overEquivCostructuredArrow_functor_obj {D : Type*} [Category D]
    {F : C ⥤ D} (hF : F.FullyFaithful) {X : C} (Y : Over X) :
    (hF.overEquivCostructuredArrow X).functor.obj Y = CostructuredArrow.mk (F.map Y.hom) := rfl

@[simp]
lemma Functor.FullyFaithful.overEquivCostructuredArrow_functor_map_left {D : Type*} [Category D]
    {F : C ⥤ D} (hF : F.FullyFaithful) {X : C} {Y Z : Over X} (f : Y ⟶ Z) :
    ((hF.overEquivCostructuredArrow X).functor.map f).left = f.left := rfl

end CategoryTheory
