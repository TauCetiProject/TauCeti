/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.Data.Fintype.BigOperators

/-!
# Binary biproduct squares

This file records generic categorical properties of binary biproducts. A biproduct map factors
through the maps obtained by changing one summand at a time, and the squares obtained by adjoining
an identity summand are pushouts or pullbacks. The biproduct of two cokernels is the cokernel of
the biproduct of the two morphisms (`CategoryTheory.Limits.CokernelCofork.isColimitBiprod`); this
is the biproduct analogue of Mathlib's `CategoryTheory.Limits.CokernelCofork.isColimitTensor`.

In a preadditive category, a zero object and binary biproducts already give all finite biproducts
(`TauCeti.hasFiniteBiproducts_of_hasBinaryBiproducts`), and a finite biproduct indexed by
`Option J` splits off its `none` summand (`TauCeti.biproductOptionIso`); the latter is the
inductive step for computing additive invariants of finite biproducts.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- A binary biproduct map factors by changing its first and second summands in succession. -/
theorem biprod_map_factor {X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
    [HasBinaryBiproduct X₁ X₂] [HasBinaryBiproduct Y₁ X₂]
    [HasBinaryBiproduct Y₁ Y₂] :
    biprod.map f g = biprod.map f (𝟙 X₂) ≫ biprod.map (𝟙 Y₁) g := by
  ext <;> simp

/-- The square formed by a morphism and the corresponding biproduct inclusions is a pushout. -/
theorem isPushout_biprod_inl_map {X Y : C} (f : X ⟶ Y) (Z : C)
    [HasBinaryBiproduct X Z] [HasBinaryBiproduct Y Z] :
    IsPushout (biprod.inl : X ⟶ X ⊞ Z) f (biprod.map f (𝟙 Z))
      (biprod.inl : Y ⟶ Y ⊞ Z) :=
  (IsPushout.of_coprod_inl_with_id f Z).of_iso
    (Iso.refl X) (biprod.isoCoprod X Z).symm
    (Iso.refl Y) (biprod.isoCoprod Y Z).symm
    (by simp [coprod.inl_desc]) (by simp) (by ext <;> simp) (by simp [coprod.inl_desc])

/-- The square formed by a morphism and the corresponding biproduct projections is a pullback. -/
theorem isPullback_biprod_map_fst {X Y : C} (f : X ⟶ Y) (Z : C)
    [HasBinaryBiproduct X Z] [HasBinaryBiproduct Y Z] :
    IsPullback (biprod.fst : X ⊞ Z ⟶ X) (biprod.map f (𝟙 Z)) f
      (biprod.fst : Y ⊞ Z ⟶ Y) :=
  (IsPullback.of_prod_fst_with_id f Z).of_iso
    (biprod.isoProd X Z).symm (Iso.refl X)
    (biprod.isoProd Y Z).symm (Iso.refl Y)
    (by simp) (by ext <;> simp) (by simp) (by simp)

section Preadditive

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- A preadditive category with a zero object and binary biproducts has all finite biproducts.
Like Mathlib's `CategoryTheory.Limits.hasBinaryBiproducts_of_finite_biproducts`, this is a theorem
rather than an instance, so that a concrete category may keep finite biproducts with better
definitional properties. -/
theorem hasFiniteBiproducts_of_hasBinaryBiproducts [HasZeroObject C] [HasBinaryBiproducts C] :
    HasFiniteBiproducts C :=
  have : HasFiniteProducts C := hasFiniteProducts_of_has_binary_and_terminal
  HasFiniteBiproducts.of_hasFiniteProducts

variable {J : Type} [Fintype J] (f : Option J → C) [HasBiproduct f]
  [HasBiproduct fun j => f (some j)] [HasBinaryBiproduct (f none) (⨁ fun j => f (some j))]

/-- A biproduct indexed by `Option J` is the binary biproduct of its `none` summand and the
biproduct of the remaining summands. -/
noncomputable def biproductOptionIso : ⨁ f ≅ f none ⊞ ⨁ fun j => f (some j) where
  hom := biprod.lift (biproduct.π f none) (biproduct.lift fun j => biproduct.π f (some j))
  inv := biprod.desc (biproduct.ι f none) (biproduct.desc fun j => biproduct.ι f (some j))
  hom_inv_id := by
    rw [biprod.lift_desc, biproduct.lift_desc, ← biproduct.total, Fintype.sum_option]
  inv_hom_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext
    · simp
    · ext j
      simp [biproduct.ι_π_ne _ (Option.some_ne_none j).symm]
    · ext j
      simp [biproduct.ι_π_ne _ (Option.some_ne_none j)]
    · ext j k
      by_cases h : k = j
      · subst h
        simp
      · simp [biproduct.ι_π_ne _ h, biproduct.ι_π_ne _ (mt Option.some_inj.mp h)]

@[simp]
theorem biproductOptionIso_hom_fst :
    (biproductOptionIso f).hom ≫ biprod.fst = biproduct.π f none := by
  simp [biproductOptionIso]

@[simp]
theorem biproductOptionIso_hom_snd_π (j : J) :
    (biproductOptionIso f).hom ≫ biprod.snd ≫ biproduct.π _ j = biproduct.π f (some j) := by
  simp [biproductOptionIso]

end Preadditive

end TauCeti

namespace CategoryTheory.Limits.CokernelCofork

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {X₁ Y₁ : C} {f₁ : X₁ ⟶ Y₁} {c₁ : CokernelCofork f₁}
  {X₂ Y₂ : C} {f₂ : X₂ ⟶ Y₂} {c₂ : CokernelCofork f₂}
  [HasBinaryBiproduct X₁ X₂] [HasBinaryBiproduct Y₁ Y₂] [HasBinaryBiproduct c₁.pt c₂.pt]

variable (c₁ c₂) in
/-- Given cokernel coforks `c₁` and `c₂` for `f₁ : X₁ ⟶ Y₁` and `f₂ : X₂ ⟶ Y₂`, this is the
cokernel cofork for `biprod.map f₁ f₂ : X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂` with point `c₁.pt ⊞ c₂.pt`. -/
noncomputable abbrev biprod : CokernelCofork (biprod.map f₁ f₂) :=
  CokernelCofork.ofπ (biprod.map c₁.π c₂.π) (by ext <;> simp)

/-- The biproduct of two colimit cokernel coforks is a colimit: `c₁.pt ⊞ c₂.pt` is the cokernel
of `biprod.map f₁ f₂`. -/
noncomputable def isColimitBiprod (hc₁ : IsColimit c₁) (hc₂ : IsColimit c₂) :
    IsColimit (c₁.biprod c₂) :=
  IsColimit.ofπ _ _
    (fun k hk ↦ biprod.desc
      (Cofork.IsColimit.desc hc₁ (biprod.inl ≫ k) (by simpa using biprod.inl ≫= hk))
      (Cofork.IsColimit.desc hc₂ (biprod.inr ≫ k) (by simpa using biprod.inr ≫= hk)))
    (fun k hk ↦ by ext <;> simp)
    (fun k hk m hm ↦ by
      subst hm
      ext
      · exact Cofork.IsColimit.hom_ext hc₁ (by simp)
      · exact Cofork.IsColimit.hom_ext hc₂ (by simp))

end CategoryTheory.Limits.CokernelCofork
