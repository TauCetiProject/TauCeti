/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Morphisms out of and into whiskered finite biproducts

In a monoidal preadditive category, whiskering is additive, so the inclusions
`biproduct.ι f j ▷ U` of the summands of `(⨁ f) ⊗ U` are jointly epimorphic and the projections
`U ◁ biproduct.π f j` of `U ⊗ ⨁ f` onto its summands are jointly monomorphic. This file records
the resulting extensionality principles for a finite index type in an arbitrary universe.
Mathlib's `CategoryTheory.rightDistributor_ext_left` and `CategoryTheory.leftDistributor_ext_right`
state the same principles for index types in `Type`, through the distributors, which are only
defined there; biproducts indexed by the isomorphism classes of simple objects of a category, for
example, need the general form. It also records `biproduct.ι_map` and `biproduct.map_π` whiskered
on the right and on the left.
-/

public section

namespace CategoryTheory.Limits.biproduct

open MonoidalCategory

variable {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]
  {J : Type*} [Finite J] {f : J → C} [HasBiproduct f]

/-- Two morphisms out of `(⨁ f) ⊗ U` agree as soon as they agree on each summand `f j ⊗ U`. -/
theorem whiskerRight_hom_ext {U Y : C} {g h : (⨁ f) ⊗ U ⟶ Y}
    (w : ∀ j, biproduct.ι f j ▷ U ≫ g = biproduct.ι f j ▷ U ≫ h) : g = h := by
  have := Fintype.ofFinite J
  have e : ∑ j, biproduct.π f j ▷ U ≫ biproduct.ι f j ▷ U = 𝟙 _ := by
    simp_rw [← comp_whiskerRight, ← sum_whiskerRight, biproduct.total, id_whiskerRight]
  rw [← Category.id_comp g, ← Category.id_comp h, ← e, Preadditive.sum_comp, Preadditive.sum_comp]
  simp only [Category.assoc, w]

/-- Two morphisms into `U ⊗ ⨁ f` agree as soon as their projections onto each summand `U ⊗ f j`
agree. -/
theorem whiskerLeft_hom_ext {U Y : C} {g h : Y ⟶ U ⊗ ⨁ f}
    (w : ∀ j, g ≫ U ◁ biproduct.π f j = h ≫ U ◁ biproduct.π f j) : g = h := by
  have := Fintype.ofFinite J
  have e : ∑ j, U ◁ biproduct.π f j ≫ U ◁ biproduct.ι f j = 𝟙 _ := by
    simp_rw [← MonoidalCategory.whiskerLeft_comp, ← whiskerLeft_sum, biproduct.total,
      MonoidalCategory.whiskerLeft_id]
  rw [← Category.comp_id g, ← Category.comp_id h, ← e, Preadditive.comp_sum, Preadditive.comp_sum]
  simp only [← Category.assoc, w]

section Map

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [MonoidalCategory C] {J : Type*}
  {f g : J → C} [HasBiproduct f] [HasBiproduct g]

/-- `biproduct.ι_map` whiskered on the right by `U`. -/
@[reassoc (attr := simp)]
theorem ι_whiskerRight_map_whiskerRight (p : ∀ j, f j ⟶ g j) (j : J) (U : C) :
    biproduct.ι f j ▷ U ≫ biproduct.map p ▷ U = p j ▷ U ≫ biproduct.ι g j ▷ U := by
  simp only [← comp_whiskerRight, biproduct.ι_map]

/-- `biproduct.map_π` whiskered on the left by `U`. -/
@[reassoc (attr := simp)]
theorem whiskerLeft_map_whiskerLeft_π (p : ∀ j, f j ⟶ g j) (j : J) (U : C) :
    U ◁ biproduct.map p ≫ U ◁ biproduct.π g j = U ◁ biproduct.π f j ≫ U ◁ p j := by
  simp only [← MonoidalCategory.whiskerLeft_comp, biproduct.map_π]

end Map

end CategoryTheory.Limits.biproduct
