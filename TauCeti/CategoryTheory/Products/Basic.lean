/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# Basic structures on product categories

This file supplies componentwise smallness, zero morphisms, and zero objects for Cartesian product
categories. These structures let additive constructions and invariants apply to products.

It also shows that pushout and pullback squares in a product category are detected
componentwise: a square in `C × D` is a pushout (resp. pullback) exactly when both of its
projected squares are (`TauCeti.isPushout_fst`, `TauCeti.isPushout_snd`,
`TauCeti.isPushout_prod`, and their pullback counterparts).
-/

public section

open CategoryTheory

namespace TauCeti

open Limits ZeroObject

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- Zero morphisms in a product category are computed componentwise. -/
instance instHasZeroMorphismsProd [HasZeroMorphisms C] [HasZeroMorphisms D] :
    HasZeroMorphisms (C × D) where
  zero := fun X Y => ⟨⟨0, 0⟩⟩
  comp_zero f Z := by ext <;> simp
  zero_comp := by intros; ext <;> simp

/-- The product of essentially small categories is essentially small. -/
noncomputable instance [EssentiallySmall.{w₁} C] [EssentiallySmall.{w₂} D] :
    EssentiallySmall.{max w₁ w₂} (C × D) :=
  EssentiallySmall.mk' ((equivSmallModel C).prod (equivSmallModel D))

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

section CommSq

variable {A A' B B' : C × D} {f : A ⟶ A'} {g : A ⟶ B} {f' : B ⟶ B'} {g' : A' ⟶ B'}

/-- The first projection of a pushout square in a product category is a pushout square. -/
theorem isPushout_fst (sq : IsPushout g f f' g') : IsPushout g.1 f.1 f'.1 g'.1 := by
  refine IsPushout.mk' (congrArg Prod.fst sq.w) ?_ ?_
  · intro T φ φ' h₁ h₂
    have h := sq.hom_ext (k := ((φ, 𝟙 B'.2) : B' ⟶ (T, B'.2))) (l := (φ', 𝟙 B'.2))
      (Prod.hom_ext h₁ rfl) (Prod.hom_ext h₂ rfl)
    exact congrArg Prod.fst h
  · intro T a b h
    have hab : g ≫ ((a, f'.2) : B ⟶ (T, B'.2)) = f ≫ ((b, g'.2) : A' ⟶ (T, B'.2)) :=
      Prod.hom_ext h (by simpa using congrArg Prod.snd sq.w)
    exact ⟨(sq.desc _ _ hab).1, congrArg Prod.fst (sq.inl_desc _ _ hab),
      congrArg Prod.fst (sq.inr_desc _ _ hab)⟩

/-- The second projection of a pushout square in a product category is a pushout square. -/
theorem isPushout_snd (sq : IsPushout g f f' g') : IsPushout g.2 f.2 f'.2 g'.2 := by
  refine IsPushout.mk' (congrArg Prod.snd sq.w) ?_ ?_
  · intro T φ φ' h₁ h₂
    have h := sq.hom_ext (k := ((𝟙 B'.1, φ) : B' ⟶ (B'.1, T))) (l := (𝟙 B'.1, φ'))
      (Prod.hom_ext rfl h₁) (Prod.hom_ext rfl h₂)
    exact congrArg Prod.snd h
  · intro T a b h
    have hab : g ≫ ((f'.1, a) : B ⟶ (B'.1, T)) = f ≫ ((g'.1, b) : A' ⟶ (B'.1, T)) :=
      Prod.hom_ext (by simpa using congrArg Prod.fst sq.w) h
    exact ⟨(sq.desc _ _ hab).2, congrArg Prod.snd (sq.inl_desc _ _ hab),
      congrArg Prod.snd (sq.inr_desc _ _ hab)⟩

/-- The first projection of a pullback square in a product category is a pullback square. -/
theorem isPullback_fst (sq : IsPullback f g g' f') : IsPullback f.1 g.1 g'.1 f'.1 := by
  refine IsPullback.mk' (congrArg Prod.fst sq.w) ?_ ?_
  · intro T φ φ' h₁ h₂
    have h := sq.hom_ext (k := ((φ, 𝟙 A.2) : (T, A.2) ⟶ A)) (l := (φ', 𝟙 A.2))
      (Prod.hom_ext h₁ rfl) (Prod.hom_ext h₂ rfl)
    exact congrArg Prod.fst h
  · intro T a b h
    have hab : ((a, f.2) : (T, A.2) ⟶ A') ≫ g' = ((b, g.2) : (T, A.2) ⟶ B) ≫ f' :=
      Prod.hom_ext h (by simpa using congrArg Prod.snd sq.w)
    exact ⟨(sq.lift _ _ hab).1, congrArg Prod.fst (sq.lift_fst _ _ hab),
      congrArg Prod.fst (sq.lift_snd _ _ hab)⟩

/-- The second projection of a pullback square in a product category is a pullback square. -/
theorem isPullback_snd (sq : IsPullback f g g' f') : IsPullback f.2 g.2 g'.2 f'.2 := by
  refine IsPullback.mk' (congrArg Prod.snd sq.w) ?_ ?_
  · intro T φ φ' h₁ h₂
    have h := sq.hom_ext (k := ((𝟙 A.1, φ) : (A.1, T) ⟶ A)) (l := (𝟙 A.1, φ'))
      (Prod.hom_ext rfl h₁) (Prod.hom_ext rfl h₂)
    exact congrArg Prod.snd h
  · intro T a b h
    have hab : ((f.1, a) : (A.1, T) ⟶ A') ≫ g' = ((g.1, b) : (A.1, T) ⟶ B) ≫ f' :=
      Prod.hom_ext (by simpa using congrArg Prod.fst sq.w) h
    exact ⟨(sq.lift _ _ hab).2, congrArg Prod.snd (sq.lift_fst _ _ hab),
      congrArg Prod.snd (sq.lift_snd _ _ hab)⟩

/-- A square in a product category whose two projections are pushout squares is a pushout
square. -/
theorem isPushout_prod (h₁ : IsPushout g.1 f.1 f'.1 g'.1) (h₂ : IsPushout g.2 f.2 f'.2 g'.2) :
    IsPushout g f f' g' := by
  refine IsPushout.mk' (Prod.hom_ext h₁.w h₂.w) ?_ ?_
  · intro T φ φ' h₁' h₂'
    exact Prod.hom_ext
      (h₁.hom_ext (congrArg Prod.fst h₁') (congrArg Prod.fst h₂'))
      (h₂.hom_ext (congrArg Prod.snd h₁') (congrArg Prod.snd h₂'))
  · intro T a b h
    exact ⟨(h₁.desc a.1 b.1 (congrArg Prod.fst h),
        h₂.desc a.2 b.2 (congrArg Prod.snd h)),
      Prod.hom_ext (h₁.inl_desc _ _ _) (h₂.inl_desc _ _ _),
      Prod.hom_ext (h₁.inr_desc _ _ _) (h₂.inr_desc _ _ _)⟩

/-- A square in a product category whose two projections are pullback squares is a pullback
square. -/
theorem isPullback_prod (h₁ : IsPullback f.1 g.1 g'.1 f'.1) (h₂ : IsPullback f.2 g.2 g'.2 f'.2) :
    IsPullback f g g' f' := by
  refine IsPullback.mk' (Prod.hom_ext h₁.w h₂.w) ?_ ?_
  · intro T φ φ' h₁' h₂'
    exact Prod.hom_ext
      (h₁.hom_ext (congrArg Prod.fst h₁') (congrArg Prod.fst h₂'))
      (h₂.hom_ext (congrArg Prod.snd h₁') (congrArg Prod.snd h₂'))
  · intro T a b h
    exact ⟨(h₁.lift a.1 b.1 (congrArg Prod.fst h),
        h₂.lift a.2 b.2 (congrArg Prod.snd h)),
      Prod.hom_ext (h₁.lift_fst _ _ _) (h₂.lift_fst _ _ _),
      Prod.hom_ext (h₁.lift_snd _ _ _) (h₂.lift_snd _ _ _)⟩

end CommSq

end TauCeti
