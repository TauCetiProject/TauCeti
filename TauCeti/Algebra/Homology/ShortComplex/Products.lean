/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import TauCeti.Algebra.Homology.ShortComplex.Biproduct

/-!
# Componentwise biproducts of short complexes

The projections of the componentwise binary sum exhibit it as a product of short complexes.
The same construction for an indexed family only needs the three biproducts of its terms.
Its componentwise inclusions and projections give both universal properties by
`CategoryTheory.ShortComplex.isLimitOfIsLimitπ` and its colimit analogue.

As for `CategoryTheory.ShortComplex.biprod`, the three terms of
`CategoryTheory.ShortComplex.biproduct` reduce to the chosen biproducts in the ambient category.
This makes the componentwise maps usable without transporting their sources and targets.
-/

public section

namespace CategoryTheory.ShortComplex

open Limits

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

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
noncomputable def isLimitBiprodFan : IsLimit (BinaryFan.mk (S.biprodFst T) (S.biprodSnd T)) :=
  isLimitOfIsLimitπ _
    ((isLimitMapConeBinaryFanEquiv π₁ _ _).symm (BinaryBiproduct.isLimit S.X₁ T.X₁))
    ((isLimitMapConeBinaryFanEquiv π₂ _ _).symm (BinaryBiproduct.isLimit S.X₂ T.X₂))
    ((isLimitMapConeBinaryFanEquiv π₃ _ _).symm (BinaryBiproduct.isLimit S.X₃ T.X₃))

end Binary

section Family

variable {J : Type*} (S : J → ShortComplex C)
  [HasBiproduct (fun j ↦ (S j).X₁)] [HasBiproduct (fun j ↦ (S j).X₂)]
  [HasBiproduct (fun j ↦ (S j).X₃)]

/-- The componentwise direct sum of a family of short complexes. -/
@[expose, simps] noncomputable def biproduct : ShortComplex C where
  f := Limits.biproduct.map fun j ↦ (S j).f
  g := Limits.biproduct.map fun j ↦ (S j).g
  zero := by ext j; simp

/-- The inclusions and projections of the componentwise direct sum. -/
@[expose, simps! pt π_τ₁ π_τ₂ π_τ₃ ι_τ₁ ι_τ₂ ι_τ₃]
noncomputable def biproductBicone : Bicone S where
  pt := biproduct S
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
noncomputable def isBilimitBiproductBicone : (biproductBicone S).IsBilimit where
  isLimit := isLimitOfIsLimitπ _
    ((isLimitMapConeFanMkEquiv π₁ S _).symm (Limits.biproduct.isLimit fun i ↦ (S i).X₁))
    ((isLimitMapConeFanMkEquiv π₂ S _).symm (Limits.biproduct.isLimit fun i ↦ (S i).X₂))
    ((isLimitMapConeFanMkEquiv π₃ S _).symm (Limits.biproduct.isLimit fun i ↦ (S i).X₃))
  isColimit := isColimitOfIsColimitπ _
    ((isColimitMapCoconeCofanMkEquiv π₁ S _).symm (Limits.biproduct.isColimit fun i ↦ (S i).X₁))
    ((isColimitMapCoconeCofanMkEquiv π₂ S _).symm (Limits.biproduct.isColimit fun i ↦ (S i).X₂))
    ((isColimitMapCoconeCofanMkEquiv π₃ S _).symm (Limits.biproduct.isColimit fun i ↦ (S i).X₃))

end Family

end CategoryTheory.ShortComplex
