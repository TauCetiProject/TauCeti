/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts

/-!
# Componentwise biproducts of short complexes

Two short complexes in a category with zero morphisms have a componentwise binary direct sum,
provided the three relevant binary biproducts exist. Its projections exhibit it as a product.
For an indexed family, the three biproducts of its terms give a bicone of short complexes.
Its projections and inclusions exhibit it as a limit and a colimit by
`CategoryTheory.ShortComplex.isLimitOfIsLimitπ` and its colimit analogue.

## Main definitions

* `CategoryTheory.ShortComplex.biprod`: the componentwise binary direct sum of two short
  complexes.
* `TauCeti.shortComplexBiproduct`: the componentwise direct sum of an indexed family.
* `TauCeti.isBilimitShortComplexBiproductBicone`: the universal properties of this sum.

## Implementation notes

`ShortComplex.biprod` is `@[expose]`d so that its objects are definitionally the corresponding
biproducts outside this file. Without that, the type of `(S₁.biprod S₂).f` could not be seen to be
`S₁.X₁ ⊞ S₂.X₁ ⟶ S₁.X₂ ⊞ S₂.X₂`, and the projection lemmas for the two maps would have to be stated
with a heterogeneous equality. The indexed sum and its bicone likewise expose their terms so
their projections and inclusions have the expected component types.
-/

public section

namespace CategoryTheory.ShortComplex

open Limits

universe v u

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- The componentwise binary direct sum of two short complexes. -/
@[expose, simps] noncomputable def biprod (S₁ S₂ : ShortComplex C)
    [HasBinaryBiproduct S₁.X₁ S₂.X₁] [HasBinaryBiproduct S₁.X₂ S₂.X₂]
    [HasBinaryBiproduct S₁.X₃ S₂.X₃] : ShortComplex C where
  f := biprod.map S₁.f S₂.f
  g := biprod.map S₁.g S₂.g
  zero := by ext <;> simp [reassoc_of% S₁.zero, reassoc_of% S₂.zero]

section Binary

variable (S T : ShortComplex C) [HasBinaryBiproduct S.X₁ T.X₁]
  [HasBinaryBiproduct S.X₂ T.X₂] [HasBinaryBiproduct S.X₃ T.X₃]

/-- The first projection of the componentwise binary direct sum. -/
noncomputable def biprodFst : S.biprod T ⟶ S :=
  homMk biprod.fst biprod.fst biprod.fst (biprod.map_fst ..).symm (biprod.map_fst ..).symm

@[simp]
theorem biprodFst_τ₁ : (S.biprodFst T).τ₁ = biprod.fst := (rfl)

@[simp]
theorem biprodFst_τ₂ : (S.biprodFst T).τ₂ = biprod.fst := (rfl)

@[simp]
theorem biprodFst_τ₃ : (S.biprodFst T).τ₃ = biprod.fst := (rfl)

/-- The second projection of the componentwise binary direct sum. -/
noncomputable def biprodSnd : S.biprod T ⟶ T :=
  homMk biprod.snd biprod.snd biprod.snd (biprod.map_snd ..).symm (biprod.map_snd ..).symm

@[simp]
theorem biprodSnd_τ₁ : (S.biprodSnd T).τ₁ = biprod.snd := (rfl)

@[simp]
theorem biprodSnd_τ₂ : (S.biprodSnd T).τ₂ = biprod.snd := (rfl)

@[simp]
theorem biprodSnd_τ₃ : (S.biprodSnd T).τ₃ = biprod.snd := (rfl)

/-- The componentwise binary sum is a product of short complexes. -/
noncomputable def isLimitBiprodFan : IsLimit (BinaryFan.mk (S.biprodFst T) (S.biprodSnd T)) := by
  refine isLimitOfIsLimitπ _
    ((isLimitMapConeBinaryFanEquiv π₁ _ _).symm ((BinaryBiproduct.isLimit S.X₁ T.X₁).ofIsoLimit ?_))
    ((isLimitMapConeBinaryFanEquiv π₂ _ _).symm ((BinaryBiproduct.isLimit S.X₂ T.X₂).ofIsoLimit ?_))
    ((isLimitMapConeBinaryFanEquiv π₃ _ _).symm ((BinaryBiproduct.isLimit S.X₃ T.X₃).ofIsoLimit ?_))
  all_goals
    refine Cone.ext (Iso.refl _) ?_
    rintro ⟨⟨⟩⟩ <;> refine Eq.trans ?_ (Category.id_comp _).symm <;> simp

end Binary

end CategoryTheory.ShortComplex

namespace TauCeti

open CategoryTheory CategoryTheory.Limits CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {J : Type*} (S : J → ShortComplex C)
  [HasBiproduct (fun j ↦ (S j).X₁)] [HasBiproduct (fun j ↦ (S j).X₂)]
  [HasBiproduct (fun j ↦ (S j).X₃)]

/-- The componentwise direct sum of a family of short complexes. -/
@[expose, simps] noncomputable def shortComplexBiproduct : ShortComplex C where
  f := Limits.biproduct.map fun j ↦ (S j).f
  g := Limits.biproduct.map fun j ↦ (S j).g
  zero := by ext j; simp

/-- The inclusions and projections of the componentwise direct sum. -/
@[expose, simps! pt π_τ₁ π_τ₂ π_τ₃ ι_τ₁ ι_τ₂ ι_τ₃]
noncomputable def shortComplexBiproductBicone : Bicone S where
  pt := shortComplexBiproduct S
  π j := homMk (Limits.biproduct.π _ j) (Limits.biproduct.π _ j) (Limits.biproduct.π _ j)
    (Limits.biproduct.map_π (fun i ↦ (S i).f) j).symm
    (Limits.biproduct.map_π (fun i ↦ (S i).g) j).symm
  ι j := homMk (Limits.biproduct.ι (fun i ↦ (S i).X₁) j)
    (Limits.biproduct.ι (fun i ↦ (S i).X₂) j) (Limits.biproduct.ι (fun i ↦ (S i).X₃) j)
    (Limits.biproduct.ι_map (fun i ↦ (S i).f) j)
    (Limits.biproduct.ι_map (fun i ↦ (S i).g) j)
  ι_π j j' := by
    split_ifs with h
    · subst j'
      ext <;> exact Limits.biproduct.ι_π_self _ _
    · ext <;> exact Limits.biproduct.ι_π_ne _ h

/-- The componentwise direct sum is a biproduct in the category of short complexes. -/
noncomputable def isBilimitShortComplexBiproductBicone :
    (shortComplexBiproductBicone S).IsBilimit where
  -- `Bicone.toCone` and `Bicone.toCocone` give the fan and cofan on the bicone's legs.
  isLimit := by
    refine isLimitOfIsLimitπ _
      ((isLimitMapConeFanMkEquiv π₁ S _).symm ((biproduct.isLimit fun i ↦ (S i).X₁).ofIsoLimit ?_))
      ((isLimitMapConeFanMkEquiv π₂ S _).symm ((biproduct.isLimit fun i ↦ (S i).X₂).ofIsoLimit ?_))
      ((isLimitMapConeFanMkEquiv π₃ S _).symm ((biproduct.isLimit fun i ↦ (S i).X₃).ofIsoLimit ?_))
    all_goals
      refine Cone.ext (Iso.refl _) ?_
      rintro ⟨j⟩
      refine Eq.trans ?_ (Category.id_comp _).symm
      simp
  isColimit := by
    refine isColimitOfIsColimitπ _
      ((isColimitMapCoconeCofanMkEquiv π₁ S _).symm
        ((biproduct.isColimit fun i ↦ (S i).X₁).ofIsoColimit ?_))
      ((isColimitMapCoconeCofanMkEquiv π₂ S _).symm
        ((biproduct.isColimit fun i ↦ (S i).X₂).ofIsoColimit ?_))
      ((isColimitMapCoconeCofanMkEquiv π₃ S _).symm
        ((biproduct.isColimit fun i ↦ (S i).X₃).ofIsoColimit ?_))
    all_goals
      refine Cocone.ext (Iso.refl _) ?_
      rintro ⟨j⟩
      refine (Category.comp_id _).trans ?_
      simp

/-- A family of short complexes has a biproduct whenever its three component families do. -/
instance hasBiproductShortComplex : HasBiproduct S :=
  HasBiproduct.mk ⟨_, isBilimitShortComplexBiproductBicone S⟩

end TauCeti
