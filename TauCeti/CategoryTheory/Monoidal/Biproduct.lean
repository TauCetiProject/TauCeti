/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Moving an object past a finite biproduct, summand by summand

In a monoidal preadditive category with finite biproducts, Mathlib's distributors
`CategoryTheory.rightDistributor` and `CategoryTheory.leftDistributor` identify `(⨁ f) ⊗ U` and
`U ⊗ ⨁ f` with the biproducts of the summands `f j ⊗ U` and `U ⊗ f j`. So a family of isomorphisms
`β j : f j ⊗ U ≅ U ⊗ f j` assembles into an isomorphism `(⨁ f) ⊗ U ≅ U ⊗ ⨁ f`,
`CategoryTheory.biproductCommIso f U β`, which restricts to `β j` on the summand `f j`.

With `β j` the components at `U` of half-braidings on the summands, these are the components of
the half-braiding on `⨁ f`, both for the Drinfeld centre and for the centre of a lax monoidal
functor; this file is the part of that construction that involves no half-braiding.

## Main declarations

* `CategoryTheory.biproductCommIso`: the isomorphism `(⨁ f) ⊗ U ≅ U ⊗ ⨁ f` assembled from
  isomorphisms on the summands, characterized by
  `CategoryTheory.biproduct_ι_comp_biproductCommIso_hom` and
  `CategoryTheory.biproductCommIso_hom_comp_biproduct_π`.
-/

public section

universe v u

namespace CategoryTheory

open MonoidalCategory Limits

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C] [MonoidalPreadditive C]
  [HasFiniteBiproducts C] {J : Type} [Finite J]

/-- The isomorphism `(⨁ f) ⊗ U ≅ U ⊗ ⨁ f` assembled from isomorphisms `β j : f j ⊗ U ≅ U ⊗ f j`
on the summands: it distributes `(⨁ f) ⊗ U` over the summands, applies the isomorphisms `β j`,
and collects `U ⊗ ⨁ f` again. -/
noncomputable def biproductCommIso (f : J → C) (U : C) (β : ∀ j, f j ⊗ U ≅ U ⊗ f j) :
    (⨁ f) ⊗ U ≅ U ⊗ ⨁ f :=
  rightDistributor f U ≪≫ biproduct.mapIso β ≪≫ (leftDistributor U f).symm

/-- On the summand `f j`, the isomorphism `biproductCommIso f U β` is `β j`. -/
@[reassoc (attr := simp)]
theorem biproduct_ι_comp_biproductCommIso_hom (f : J → C) (U : C)
    (β : ∀ j, f j ⊗ U ≅ U ⊗ f j) (j : J) :
    biproduct.ι f j ▷ U ≫ (biproductCommIso f U β).hom = (β j).hom ≫ U ◁ biproduct.ι f j := by
  simp [biproductCommIso]

/-- Projected to the summand `f j`, the isomorphism `biproductCommIso f U β` is `β j`. -/
@[reassoc (attr := simp)]
theorem biproductCommIso_hom_comp_biproduct_π (f : J → C) (U : C)
    (β : ∀ j, f j ⊗ U ≅ U ⊗ f j) (j : J) :
    (biproductCommIso f U β).hom ≫ U ◁ biproduct.π f j = biproduct.π f j ▷ U ≫ (β j).hom := by
  simp [biproductCommIso]

end CategoryTheory
