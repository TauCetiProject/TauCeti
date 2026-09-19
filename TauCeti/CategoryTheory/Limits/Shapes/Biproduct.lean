/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Binary biproduct squares

This file records generic categorical properties of binary biproducts. A biproduct map factors
through the maps obtained by changing one summand at a time, and the squares obtained by adjoining
an identity summand are pushouts or pullbacks. The biproduct of two cokernels is the cokernel of
the biproduct of the two morphisms (`CategoryTheory.Limits.CokernelCofork.isColimitBiprod`); this
is the biproduct analogue of Mathlib's `CategoryTheory.Limits.CokernelCofork.isColimitTensor`.
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
