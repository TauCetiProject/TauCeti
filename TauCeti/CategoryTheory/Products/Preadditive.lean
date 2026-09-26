/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import TauCeti.CategoryTheory.Products.Basic

/-!
# Products of preadditive categories

This file equips product categories with componentwise binary biproducts and, when the factors
are preadditive, a componentwise preadditive structure and additive projection and product
functors. These constructions let additive invariants, including split Grothendieck groups,
compare a product category with its factors.
-/

public section

open CategoryTheory

namespace TauCeti

open Limits ZeroObject

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- The componentwise preadditive structure on a product category. -/
instance instPreadditiveProd [Preadditive C] [Preadditive D] : Preadditive (C × D) where
  homGroup X Y := inferInstanceAs (AddCommGroup ((X.1 ⟶ Y.1) × (X.2 ⟶ Y.2)))
  add_comp _ _ _ _ _ _ := by ext <;> simp
  comp_add _ _ _ _ _ _ := by ext <;> simp

section BinaryBiproducts

variable [HasZeroMorphisms C] [HasZeroMorphisms D]
  [HasBinaryBiproducts C] [HasBinaryBiproducts D]

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
    (prodBinaryBicone P Q).IsBilimit := by
  -- `BinaryFan` and `BinaryCofan` express their equations through the walking-pair diagram.
  -- After selecting a product coordinate, `change` unfolds those diagram maps to the bicone
  -- fields, which are definitionally the displayed componentwise biproduct maps.
  refine ⟨BinaryFan.IsLimit.mk _
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
          exact h), BinaryCofan.IsColimit.mk _
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
          exact h)⟩

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
      -- The constant component of `sectL.map` is the identity of the inserted zero object.
      change 𝟙 (0 : D) = 𝟙 (0 : D) + 𝟙 (0 : D)
      simp

/-- Inserting a zero object in the first coordinate is an additive functor. -/
instance [HasZeroObject C] : (_root_.CategoryTheory.Prod.sectR (0 : C) D).Additive where
  map_add := by
    intro X Y f g
    apply Prod.hom_ext
    · rw [Prod.fst_add]
      -- The constant component of `sectR.map` is the identity of the inserted zero object.
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
