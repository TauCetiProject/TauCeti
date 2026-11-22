/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.SetTheory.Cardinal.Finite

import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Basic structures on product categories

This file supplies componentwise smallness, zero morphisms, and zero objects for Cartesian product
categories. These structures let additive constructions and invariants apply to products.

It also shows that pushout and pullback squares in a product category are detected
componentwise: a square in `C × D` is a pushout (resp. pullback) exactly when both of its
projected squares are (`CategoryTheory.IsPushout.fst`, `CategoryTheory.IsPushout.snd`,
`CategoryTheory.IsPushout.prod`, and their pullback counterparts). Epimorphisms and monomorphisms
in `C × D` are likewise characterized componentwise (`CategoryTheory.Prod.epi_iff`,
`CategoryTheory.Prod.mono_iff`), and the projections `Prod.fst C D` and `Prod.snd C D` preserve
epimorphisms, monomorphisms, limits of arbitrary size, and colimits of arbitrary size.

Finally, an isomorphism of pairs is a pair of isomorphisms (`CategoryTheory.Prod.isoEquiv`), so
the automorphism group of a pair `(x, y)` has cardinality `#Aut x * #Aut y`
(`TauCeti.natCard_aut_prod`).
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
  comp_zero _ _ := by ext <;> simp
  zero_comp _ _ _ _ := by ext <;> simp

/-- The product of essentially small categories is essentially small. -/
noncomputable instance [EssentiallySmall.{w₁} C] [EssentiallySmall.{w₂} D] :
    EssentiallySmall.{max w₁ w₂} (C × D) :=
  EssentiallySmall.mk' ((equivSmallModel C).prod (equivSmallModel D))

/-- A pair of zero objects is a zero object of the product category. -/
instance [HasZeroObject C] [HasZeroObject D] : HasZeroObject (C × D) where
  zero := ⟨(0, 0),
    { unique_to _ := ⟨⟨⟨(default, default)⟩, fun _ =>
        Prod.hom_ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩⟩
      unique_from _ := ⟨⟨⟨(default, default)⟩, fun _ =>
        Prod.hom_ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩⟩ }⟩

end TauCeti

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {A A' B B' : C × D} {f : A ⟶ A'} {g : A ⟶ B} {f' : B ⟶ B'} {g' : A' ⟶ B'}

namespace IsPushout

/-- The first projection of a pushout square in a product category is a pushout square. -/
theorem fst (sq : IsPushout g f f' g') : IsPushout g.1 f.1 f'.1 g'.1 := by
  refine IsPushout.mk' (congrArg _root_.Prod.fst sq.w) ?_ ?_
  · intro T φ φ' h₁ h₂
    have h := sq.hom_ext (k := ((φ, 𝟙 B'.2) : B' ⟶ (T, B'.2))) (l := (φ', 𝟙 B'.2))
      (Prod.hom_ext h₁ rfl) (Prod.hom_ext h₂ rfl)
    exact congrArg _root_.Prod.fst h
  · intro T a b h
    have hab : g ≫ ((a, f'.2) : B ⟶ (T, B'.2)) = f ≫ ((b, g'.2) : A' ⟶ (T, B'.2)) :=
      Prod.hom_ext h (by simpa using congrArg _root_.Prod.snd sq.w)
    exact ⟨(sq.desc _ _ hab).1, congrArg _root_.Prod.fst (sq.inl_desc _ _ hab),
      congrArg _root_.Prod.fst (sq.inr_desc _ _ hab)⟩

/-- The second projection of a pushout square in a product category is a pushout square. -/
theorem snd (sq : IsPushout g f f' g') : IsPushout g.2 f.2 f'.2 g'.2 :=
  -- `Prod.swap C D` sends a morphism `(a, b)` to `(b, a)` by definition, so the first
  -- projection of the swapped square is the second projection of `sq`.
  (sq.map (Prod.swap C D)).fst

/-- A square in a product category whose two projections are pushout squares is a pushout
square. -/
theorem prod (h₁ : IsPushout g.1 f.1 f'.1 g'.1) (h₂ : IsPushout g.2 f.2 f'.2 g'.2) :
    IsPushout g f f' g' := by
  refine IsPushout.mk' (Prod.hom_ext h₁.w h₂.w) ?_ ?_
  · intro T φ φ' h₁' h₂'
    exact Prod.hom_ext
      (h₁.hom_ext (congrArg _root_.Prod.fst h₁') (congrArg _root_.Prod.fst h₂'))
      (h₂.hom_ext (congrArg _root_.Prod.snd h₁') (congrArg _root_.Prod.snd h₂'))
  · intro T a b h
    exact ⟨(h₁.desc a.1 b.1 (congrArg _root_.Prod.fst h),
        h₂.desc a.2 b.2 (congrArg _root_.Prod.snd h)),
      Prod.hom_ext (h₁.inl_desc _ _ _) (h₂.inl_desc _ _ _),
      Prod.hom_ext (h₁.inr_desc _ _ _) (h₂.inr_desc _ _ _)⟩

end IsPushout

namespace IsPullback

/-- The first projection of a pullback square in a product category is a pullback square. -/
theorem fst (sq : IsPullback f g g' f') : IsPullback f.1 g.1 g'.1 f'.1 := by
  refine IsPullback.mk' (congrArg _root_.Prod.fst sq.w) ?_ ?_
  · intro T φ φ' h₁ h₂
    have h := sq.hom_ext (k := ((φ, 𝟙 A.2) : (T, A.2) ⟶ A)) (l := (φ', 𝟙 A.2))
      (Prod.hom_ext h₁ rfl) (Prod.hom_ext h₂ rfl)
    exact congrArg _root_.Prod.fst h
  · intro T a b h
    have hab : ((a, f.2) : (T, A.2) ⟶ A') ≫ g' = ((b, g.2) : (T, A.2) ⟶ B) ≫ f' :=
      Prod.hom_ext h (by simpa using congrArg _root_.Prod.snd sq.w)
    exact ⟨(sq.lift _ _ hab).1, congrArg _root_.Prod.fst (sq.lift_fst _ _ hab),
      congrArg _root_.Prod.fst (sq.lift_snd _ _ hab)⟩

/-- The second projection of a pullback square in a product category is a pullback square. -/
theorem snd (sq : IsPullback f g g' f') : IsPullback f.2 g.2 g'.2 f'.2 :=
  -- `Prod.swap C D` sends a morphism `(a, b)` to `(b, a)` by definition, so the first
  -- projection of the swapped square is the second projection of `sq`.
  (sq.map (Prod.swap C D)).fst

/-- A square in a product category whose two projections are pullback squares is a pullback
square. -/
theorem prod (h₁ : IsPullback f.1 g.1 g'.1 f'.1) (h₂ : IsPullback f.2 g.2 g'.2 f'.2) :
    IsPullback f g g' f' := by
  refine IsPullback.mk' (Prod.hom_ext h₁.w h₂.w) ?_ ?_
  · intro T φ φ' h₁' h₂'
    exact Prod.hom_ext
      (h₁.hom_ext (congrArg _root_.Prod.fst h₁') (congrArg _root_.Prod.fst h₂'))
      (h₂.hom_ext (congrArg _root_.Prod.snd h₁') (congrArg _root_.Prod.snd h₂'))
  · intro T a b h
    exact ⟨(h₁.lift a.1 b.1 (congrArg _root_.Prod.fst h),
        h₂.lift a.2 b.2 (congrArg _root_.Prod.snd h)),
      Prod.hom_ext (h₁.lift_fst _ _ _) (h₂.lift_fst _ _ _),
      Prod.hom_ext (h₁.lift_snd _ _ _) (h₂.lift_snd _ _ _)⟩

end IsPullback

namespace Prod

universe w w'

/-- A morphism in a Cartesian product of categories is an epimorphism if and only if both of its
components are epimorphisms. -/
theorem epi_iff {X Y : C × D} (f : X ⟶ Y) : Epi f ↔ Epi f.1 ∧ Epi f.2 := by
  refine ⟨fun hf ↦ ⟨⟨fun g₁ g₂ h ↦ ?_⟩, ⟨fun g₁ g₂ h ↦ ?_⟩⟩,
    fun ⟨h₁, h₂⟩ ↦ ⟨fun g₁ g₂ h ↦ Prod.hom_ext
      ((cancel_epi f.1).1 (congrArg _root_.Prod.fst h))
      ((cancel_epi f.2).1 (congrArg _root_.Prod.snd h))⟩⟩
  · have h' : f ≫ (g₁ ×ₘ 𝟙 Y.2) = f ≫ (g₂ ×ₘ 𝟙 Y.2) := Prod.hom_ext h rfl
    exact congrArg _root_.Prod.fst ((cancel_epi f).1 h')
  · have h' : f ≫ (𝟙 Y.1 ×ₘ g₁) = f ≫ (𝟙 Y.1 ×ₘ g₂) := Prod.hom_ext rfl h
    exact congrArg _root_.Prod.snd ((cancel_epi f).1 h')

/-- A morphism in a Cartesian product of categories is a monomorphism if and only if both of its
components are monomorphisms. -/
theorem mono_iff {X Y : C × D} (f : X ⟶ Y) : Mono f ↔ Mono f.1 ∧ Mono f.2 := by
  refine ⟨fun hf ↦ ⟨⟨fun g₁ g₂ h ↦ ?_⟩, ⟨fun g₁ g₂ h ↦ ?_⟩⟩,
    fun ⟨h₁, h₂⟩ ↦ ⟨fun g₁ g₂ h ↦ Prod.hom_ext
      ((cancel_mono f.1).1 (congrArg _root_.Prod.fst h))
      ((cancel_mono f.2).1 (congrArg _root_.Prod.snd h))⟩⟩
  · have h' : (g₁ ×ₘ 𝟙 X.2) ≫ f = (g₂ ×ₘ 𝟙 X.2) ≫ f := Prod.hom_ext h rfl
    exact congrArg _root_.Prod.fst ((cancel_mono f).1 h')
  · have h' : (𝟙 X.1 ×ₘ g₁) ≫ f = (𝟙 X.1 ×ₘ g₂) ≫ f := Prod.hom_ext rfl h
    exact congrArg _root_.Prod.snd ((cancel_mono f).1 h')

/-- The first projection `C × D ⥤ C` preserves epimorphisms. -/
instance preservesEpimorphisms_fst : (Prod.fst C D).PreservesEpimorphisms where
  preserves f _ := ((epi_iff f).1 ‹_›).1

/-- The second projection `C × D ⥤ D` preserves epimorphisms. -/
instance preservesEpimorphisms_snd : (Prod.snd C D).PreservesEpimorphisms where
  preserves f _ := ((epi_iff f).1 ‹_›).2

/-- The first projection `C × D ⥤ C` preserves monomorphisms. -/
instance preservesMonomorphisms_fst : (Prod.fst C D).PreservesMonomorphisms where
  preserves f _ := ((mono_iff f).1 ‹_›).1

/-- The second projection `C × D ⥤ D` preserves monomorphisms. -/
instance preservesMonomorphisms_snd : (Prod.snd C D).PreservesMonomorphisms where
  preserves f _ := ((mono_iff f).1 ‹_›).2

/-- The first projection `C × D ⥤ C` preserves limits of any size. -/
instance preservesLimitsOfSize_fst : Limits.PreservesLimitsOfSize.{w', w} (Prod.fst C D) where
  preservesLimitsOfShape {_} _ :=
    { preservesLimit {F} := ⟨fun {c} hc ↦
        let cone (s : Limits.Cone (F ⋙ Prod.fst C D)) : Limits.Cone F :=
          { pt := (s.pt, c.pt.2)
            π :=
              { app k := s.π.app k ×ₘ (c.π.app k).2
                naturality _ _ u :=
                  Prod.hom_ext (s.π.naturality u) (((Prod.snd C D).mapCone c).π.naturality u) } }
        ⟨{ lift s := (hc.lift (cone s)).1
           fac s k := congrArg _root_.Prod.fst (hc.fac (cone s) k)
           uniq s m hm := congrArg _root_.Prod.fst <|
             hc.uniq (cone s) (m ×ₘ 𝟙 c.pt.2) fun k ↦
               Prod.hom_ext (hm k) (Category.id_comp _) }⟩⟩ }

/-- The second projection `C × D ⥤ D` preserves limits of any size. -/
instance preservesLimitsOfSize_snd : Limits.PreservesLimitsOfSize.{w', w} (Prod.snd C D) :=
  Limits.preservesLimits_of_natIso (F := Prod.swap C D ⋙ Prod.fst D C)
    (NatIso.ofComponents fun _ ↦ Iso.refl _)

/-- The first projection `C × D ⥤ C` preserves colimits of any size. -/
instance preservesColimitsOfSize_fst : Limits.PreservesColimitsOfSize.{w', w} (Prod.fst C D) where
  preservesColimitsOfShape {_} _ :=
    { preservesColimit {F} := ⟨fun {c} hc ↦
        let cocone (s : Limits.Cocone (F ⋙ Prod.fst C D)) : Limits.Cocone F :=
          { pt := (s.pt, c.pt.2)
            ι :=
              { app k := s.ι.app k ×ₘ (c.ι.app k).2
                naturality _ _ u :=
                  Prod.hom_ext (s.ι.naturality u) (((Prod.snd C D).mapCocone c).ι.naturality u) } }
        ⟨{ desc s := (hc.desc (cocone s)).1
           fac s k := congrArg _root_.Prod.fst (hc.fac (cocone s) k)
           uniq s m hm := congrArg _root_.Prod.fst <|
             hc.uniq (cocone s) (m ×ₘ 𝟙 c.pt.2) fun k ↦
               Prod.hom_ext (hm k) (Category.comp_id _) }⟩⟩ }

/-- The second projection `C × D ⥤ D` preserves colimits of any size. -/
instance preservesColimitsOfSize_snd : Limits.PreservesColimitsOfSize.{w', w} (Prod.snd C D) :=
  Limits.preservesColimits_of_natIso (F := Prod.swap C D ⋙ Prod.fst D C)
    (NatIso.ofComponents fun _ ↦ Iso.refl _)

end Prod

end CategoryTheory

namespace CategoryTheory.Prod

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- An isomorphism between pairs of objects of a product category is a pair of isomorphisms. -/
def isoEquiv {x x' : C} {y y' : D} : ((x, y) ≅ (x', y')) ≃ (x ≅ x') × (y ≅ y') where
  toFun e := ((CategoryTheory.Prod.fst C D).mapIso e, (CategoryTheory.Prod.snd C D).mapIso e)
  invFun p := Iso.prod p.1 p.2
  left_inv _ := by ext <;> rfl
  right_inv _ := by ext <;> rfl

@[simp]
theorem isoEquiv_apply {x x' : C} {y y' : D} (e : (x, y) ≅ (x', y')) :
    isoEquiv e =
      ((CategoryTheory.Prod.fst C D).mapIso e, (CategoryTheory.Prod.snd C D).mapIso e) := (rfl)

@[simp]
theorem isoEquiv_symm_apply {x x' : C} {y y' : D} (p : (x ≅ x') × (y ≅ y')) :
    isoEquiv.symm p = Iso.prod p.1 p.2 := (rfl)

end CategoryTheory.Prod

namespace TauCeti

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- The automorphism group of a pair `(x, y)` has cardinality `#Aut x * #Aut y`. -/
@[simp]
theorem natCard_aut_prod (x : C) (y : D) :
    Nat.card (Aut (x, y)) = Nat.card (Aut x) * Nat.card (Aut y) := by
  rw [← Nat.card_prod]
  exact Nat.card_congr <|
    Aut.isoEquiv.trans <| Prod.isoEquiv.trans (Aut.isoEquiv.prodCongr Aut.isoEquiv).symm

end TauCeti
