/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Products of preadditive categories

This file equips the Cartesian product of two preadditive categories with its componentwise
preadditive structure. Zero objects and binary biproducts are also constructed componentwise,
and the standard projection and product functors are shown to be additive.
-/

public section

open CategoryTheory

namespace TauCeti

open Limits ZeroObject

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- The product of essentially small categories is essentially small. -/
noncomputable instance [EssentiallySmall.{w₁} C] [EssentiallySmall.{w₂} D] :
    EssentiallySmall.{max w₁ w₂} (C × D) :=
  EssentiallySmall.mk' ((equivSmallModel C).prod (equivSmallModel D))

/-- The componentwise preadditive structure on a product category. -/
instance instPreadditiveProd [Preadditive C] [Preadditive D] : Preadditive (C × D) where
  homGroup X Y := inferInstanceAs (AddCommGroup ((X.1 ⟶ Y.1) × (X.2 ⟶ Y.2)))
  add_comp _ _ _ _ _ _ := by ext <;> simp
  comp_add _ _ _ _ _ _ := by ext <;> simp

/-- A pair of zero objects is a zero object of the product category. -/
instance [HasZeroObject C] [HasZeroObject D] : HasZeroObject (C × D) where
  zero := ⟨(0, 0),
    { unique_to := fun X =>
        ⟨⟨⟨(isZero_zero C).to_ X.1, (isZero_zero D).to_ X.2⟩, fun f => by
            exact Prod.hom_ext ((isZero_zero C).eq_of_src _ _)
              ((isZero_zero D).eq_of_src _ _)⟩⟩
      unique_from := fun X =>
        ⟨⟨⟨(isZero_zero C).from_ X.1, (isZero_zero D).from_ X.2⟩, fun f => by
            exact Prod.hom_ext ((isZero_zero C).eq_of_tgt _ _)
              ((isZero_zero D).eq_of_tgt _ _)⟩⟩ } ⟩

section BinaryBiproducts

variable [Preadditive C] [Preadditive D] [HasBinaryBiproducts C] [HasBinaryBiproducts D]

private noncomputable def prodBinaryBicone (P Q : C × D) : BinaryBicone P Q where
  pt := (P.1 ⊞ Q.1, P.2 ⊞ Q.2)
  fst := (biprod.fst, biprod.fst)
  snd := (biprod.snd, biprod.snd)
  inl := (biprod.inl, biprod.inl)
  inr := (biprod.inr, biprod.inr)
  inl_fst := by ext <;> simp
  inl_snd := by ext <;> simp
  inr_fst := by ext <;> simp
  inr_snd := by ext <;> simp

private noncomputable def prodBinaryBiconeIsBilimit (P Q : C × D) :
    (prodBinaryBicone P Q).IsBilimit where
  isLimit := BinaryFan.IsLimit.mk _
    (fun f g => (biprod.lift f.1 g.1, biprod.lift f.2 g.2))
    (fun _ _ => by ext <;> simp [prodBinaryBicone])
    (fun _ _ => by ext <;> simp [prodBinaryBicone])
    (fun f g m h₁ h₂ => by
      apply Prod.hom_ext
      · apply biprod.hom_ext
        · rw [biprod.lift_fst]
          have h := congrArg (fun p => p.1) h₁
          change m.1 ≫ biprod.fst = f.1 at h
          exact h
        · rw [biprod.lift_snd]
          have h := congrArg (fun p => p.1) h₂
          change m.1 ≫ biprod.snd = g.1 at h
          exact h
      · apply biprod.hom_ext
        · rw [biprod.lift_fst]
          have h := congrArg (fun p => p.2) h₁
          change m.2 ≫ biprod.fst = f.2 at h
          exact h
        · rw [biprod.lift_snd]
          have h := congrArg (fun p => p.2) h₂
          change m.2 ≫ biprod.snd = g.2 at h
          exact h)
  isColimit := BinaryCofan.IsColimit.mk _
    (fun f g => (biprod.desc f.1 g.1, biprod.desc f.2 g.2))
    (fun _ _ => by ext <;> simp [prodBinaryBicone])
    (fun _ _ => by ext <;> simp [prodBinaryBicone])
    (fun f g m h₁ h₂ => by
      apply Prod.hom_ext
      · apply biprod.hom_ext'
        · rw [biprod.inl_desc]
          have h := congrArg (fun p => p.1) h₁
          change biprod.inl ≫ m.1 = f.1 at h
          exact h
        · rw [biprod.inr_desc]
          have h := congrArg (fun p => p.1) h₂
          change biprod.inr ≫ m.1 = g.1 at h
          exact h
      · apply biprod.hom_ext'
        · rw [biprod.inl_desc]
          have h := congrArg (fun p => p.2) h₁
          change biprod.inl ≫ m.2 = f.2 at h
          exact h
        · rw [biprod.inr_desc]
          have h := congrArg (fun p => p.2) h₂
          change biprod.inr ≫ m.2 = g.2 at h
          exact h)

/-- Binary biproducts in a product category are computed componentwise. -/
noncomputable instance : HasBinaryBiproducts (C × D) where
  has_binary_biproduct P Q := HasBinaryBiproduct.mk
    { bicone := prodBinaryBicone P Q
      isBilimit := prodBinaryBiconeIsBilimit P Q }

end BinaryBiproducts

section AdditiveFunctors

variable [Preadditive C] [Preadditive D]

/-- The first projection from a product of preadditive categories is additive. -/
instance : (_root_.CategoryTheory.Prod.fst C D).Additive where
  map_add := rfl

/-- The second projection from a product of preadditive categories is additive. -/
instance : (_root_.CategoryTheory.Prod.snd C D).Additive where
  map_add := rfl

/-- Inserting a zero object in the second coordinate is an additive functor. -/
instance [HasZeroObject D] : (_root_.CategoryTheory.Prod.sectL C (0 : D)).Additive where
  map_add := by
    intro X Y f g
    apply Prod.hom_ext
    · rw [Prod.fst_add]
      rfl
    · rw [Prod.snd_add]
      change 𝟙 (0 : D) = 𝟙 (0 : D) + 𝟙 (0 : D)
      simp

/-- Inserting a zero object in the first coordinate is an additive functor. -/
instance [HasZeroObject C] : (_root_.CategoryTheory.Prod.sectR (0 : C) D).Additive where
  map_add := by
    intro X Y f g
    apply Prod.hom_ext
    · rw [Prod.fst_add]
      change 𝟙 (0 : C) = 𝟙 (0 : C) + 𝟙 (0 : C)
      simp
    · rw [Prod.snd_add]
      rfl

variable {C' : Type*} [Category* C'] [Preadditive C']
  {D' : Type*} [Category* D'] [Preadditive D']

/-- The product of two additive functors is additive. -/
instance (F : C ⥤ C') (G : D ⥤ D') [F.Additive] [G.Additive] : (F.prod G).Additive where
  map_add := by
    intro X Y f g
    ext
    · exact F.map_add
    · exact G.map_add

end AdditiveFunctors

end TauCeti
