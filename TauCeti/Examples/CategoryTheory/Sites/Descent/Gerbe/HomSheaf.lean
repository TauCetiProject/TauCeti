/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.Data.ZMod.Defs
public import TauCeti.CategoryTheory.Sites.Descent.Gerbe.HomSheaf

/-!
# Checks for the sheaves of morphisms of a band-preserving morphism of gerbes

For a strong transformation `η : F ⟶ G`, the identity transformation induces the identity of the
presheaf of morphisms, and the transport commutes with `pullHom` for an arbitrary local morphism.
For a band-preserving morphism of gerbes, the inverse of the isomorphism of sheaves of morphisms
undoes the forward map on every local arrow and conversely, two local arrows with the same
transport are equal, and an empty source `Hom` type forces an empty target `Hom` type, with no
anchor supplied.

A functor on a one-object category that does not act as the identity on automorphisms (the band)
need not be full: the one-object functor of the constant monoid endomorphism of
`Multiplicative (ZMod 2)` is not full.
-/

public section

namespace TauCeti.Examples.GerbeHomSheaf

open CategoryTheory CategoryTheory.Pseudofunctor CategoryTheory.Pseudofunctor.GerbeMorphismPullback
  CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat Opposite Bicategory

universe w v u v' u'

variable {C : Type u} [Category.{v} C] {F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  (η : StrongTrans F G) {U : C} {x y : F.obj (.mk (op U))}

/-- The identity transformation induces the identity of the presheaf of morphisms. -/
example : homPresheafMap (StrongTrans.id F) x y = 𝟙 _ :=
  homPresheafMap_id

/-- The transport of the pullback of an arbitrary local morphism is the pullback of its
transport. -/
example {V W : C} (f : V ⟶ U)
    (p : (F.map f.op.toLoc).toFunctor.obj x ⟶ (F.map f.op.toLoc).toFunctor.obj y) (g : W ⟶ V) :
    homMap η (g ≫ f) (pullHom p g (g ≫ f) (g ≫ f)) = pullHom (homMap η f p) g (g ≫ f) (g ≫ f) :=
  homMap_pullHom η f p g _ rfl

/-- At the identity slice, the map on presheaves of morphisms is `η_U.map`. -/
example (p : x ⟶ y) :
    (homPresheafMap η x y).app (op (Over.mk (𝟙 U))) (F.presheafHomObjHomEquiv p) =
      G.presheafHomObjHomEquiv ((η.app (.mk (op U))).toFunctor.map p) :=
  homPresheafMap_app_presheafHomObjHomEquiv η p

section Banded

variable (J : GrothendieckTopology C) {A : Sheaf J AddCommGrpCat.{w}}
  (bF : F.AbelianBanding J A) (bG : G.AbelianBanding J A) [BandPreserving bF bG η]
  [F.IsGerbe J] [G.IsGerbe J]

/-- The inverse of the isomorphism of sheaves of morphisms undoes the forward map on every local
source arrow. -/
example (T : (Over U)ᵒᵖ) (p : (F.presheafHom x y).obj T) :
    (homSheafIso η J bF bG x y).inv.hom.app T ((homSheafIso η J bF bG x y).hom.hom.app T p) =
      p :=
  congr_arg (fun φ : F.sheafHom J x y ⟶ F.sheafHom J x y ↦ φ.hom.app T p)
    (homSheafIso η J bF bG x y).hom_inv_id

/-- The forward map undoes the inverse on every local target arrow. -/
example (T : (Over U)ᵒᵖ)
    (q : (G.presheafHom ((η.app (.mk (op U))).toFunctor.obj x)
      ((η.app (.mk (op U))).toFunctor.obj y)).obj T) :
    (homSheafIso η J bF bG x y).hom.hom.app T ((homSheafIso η J bF bG x y).inv.hom.app T q) =
      q :=
  congr_arg (fun φ ↦ φ.hom.app T q) (homSheafIso η J bF bG x y).inv_hom_id

/-- Two local source arrows with the same transport are equal. -/
example (T : (Over U)ᵒᵖ) (p q : (F.presheafHom x y).obj T)
    (h : (homPresheafMap η x y).app T p = (homPresheafMap η x y).app T q) : p = q :=
  homPresheafMap_injective η bF bG T h

/-- If there is no morphism `x ⟶ y`, there is no morphism `η_U x ⟶ η_U y`: no global anchor is
smuggled in. -/
example (h : IsEmpty (x ⟶ y)) :
    IsEmpty ((η.app (.mk (op U))).toFunctor.obj x ⟶ (η.app (.mk (op U))).toFunctor.obj y) :=
  ⟨fun q ↦ h.false ((BandedMorphism.map_bijective bF bG η x y).2 q).choose⟩

end Banded

/-- A functor on a one-object category that does not act as the identity on automorphisms (the
band) need not be full: the one-object functor of the constant monoid endomorphism of
`Multiplicative (ZMod 2)` is not full. -/
example : ¬ (SingleObj.mapHom (Multiplicative (ZMod 2)) (Multiplicative (ZMod 2)) 1).Full := by
  intro hfull
  obtain ⟨_, ha⟩ := hfull.map_surjective
    (show SingleObj.star (Multiplicative (ZMod 2)) ⟶ SingleObj.star _ from .ofAdd 1)
  have h1 : (1 : Multiplicative (ZMod 2)) ≠ .ofAdd 1 := by decide
  exact h1 ha

end TauCeti.Examples.GerbeHomSheaf
