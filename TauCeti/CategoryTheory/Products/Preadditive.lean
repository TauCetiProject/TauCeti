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
compare a product category with its factors. Every object of such a product is the biproduct of
its two zero-padded components (`CategoryTheory.prod.biprodComponentsIso`).
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

namespace CategoryTheory.prod

open Limits ZeroObject

variable {C : Type*} [Category* C] {D : Type*} [Category* D]
  [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroObject C] [HasZeroObject D]
  [HasBinaryBiproducts C] [HasBinaryBiproducts D]

/-- An object of a product of categories with zero morphisms and zero objects is the biproduct
of its two components, each padded by a zero object in the other coordinate. -/
noncomputable def biprodComponentsIso (X : C × D) : (X.1, (0 : D)) ⊞ ((0 : C), X.2) ≅ X :=
  let A : C × D := (X.1, (0 : D))
  let B : C × D := ((0 : C), X.2)
  let b : BinaryBicone A B :=
    { pt := X
      fst := (𝟙 X.1, 0)
      snd := (0, 𝟙 X.2)
      inl := (𝟙 X.1, 0)
      inr := (0, 𝟙 X.2)
      inl_fst := by
        apply Prod.hom_ext
        · simp [A]
        · simp [A]
      inl_snd := by ext
      inr_fst := by ext
      inr_snd := by
        apply Prod.hom_ext
        · simp [B]
        · simp [B] }
  let hb : b.IsBilimit := by
    refine ⟨BinaryFan.IsLimit.mk _
      (fun f g => (f.1, g.2))
      (fun f _ => by
        apply Prod.hom_ext
        · simp [b, A]
        · exact (isZero_zero D).eq_of_tgt _ _)
      (fun _ g => by
        apply Prod.hom_ext
        · exact (isZero_zero C).eq_of_tgt _ _
        · simp [b, B])
      (fun f g m h₁ h₂ => by
        dsimp [b] at m h₁ h₂ ⊢
        apply Prod.hom_ext
        · simpa using congrArg (fun p => p.1) h₁
        · simpa using congrArg (fun p => p.2) h₂),
      BinaryCofan.IsColimit.mk _
      (fun f g => (f.1, g.2))
      (fun f _ => by
        apply Prod.hom_ext
        · simp [b, A]
        · exact (isZero_zero D).eq_of_src _ _)
      (fun _ g => by
        apply Prod.hom_ext
        · exact (isZero_zero C).eq_of_src _ _
        · simp [b, B])
      (fun f g m h₁ h₂ => by
        dsimp [b] at m h₁ h₂ ⊢
        apply Prod.hom_ext
        · simpa using congrArg (fun p => p.1) h₁
        · simpa using congrArg (fun p => p.2) h₂)⟩
  (biprod.uniqueUpToIso A B hb).symm

/-- The forward map of `biprodComponentsIso` is induced by the two coordinate inclusions. -/
@[simp]
theorem biprodComponentsIso_hom (X : C × D) :
    (biprodComponentsIso X).hom = biprod.desc (𝟙 X.1, 0) (0, 𝟙 X.2) := (rfl)

/-- The inverse of `biprodComponentsIso` is induced by the two coordinate projections. -/
@[simp]
theorem biprodComponentsIso_inv (X : C × D) :
    (biprodComponentsIso X).inv = biprod.lift (𝟙 X.1, 0) (0, 𝟙 X.2) := (rfl)

end CategoryTheory.prod
