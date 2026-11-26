/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Pullback.Stalk

import TauCeti.CategoryTheory.Monoidal.NaturalTransformation

/-!
# Composition coherence for pullback of sheaves of modules

The canonical comparison from successive pullbacks to pullback along the composite morphism of
ringed spaces respects the strong symmetric monoidal structures. Its unit and tensor
compatibilities are the canonical oplax composition formulas for pullback.

* `SheafOfModules.pullbackCompBraided` equips pullback along the composite site functor with the
  braided structure of pullback along the composite map of spaces.
* `TauCeti.SheafOfModules.isMonoidal_pullbackComp_hom` states that the canonical composition
  comparison is monoidal. The inverse inherits monoidality through Mathlib's natural-isomorphism
  API.
-/

public section

open CategoryTheory MonoidalCategory TopologicalSpace
open Functor.OplaxMonoidal Functor.LaxMonoidal

universe u

namespace TauCeti.SheafOfModules

open _root_.SheafOfModules

noncomputable section

variable {X Y : TopCat.{u}}
  {𝒪X : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  {𝒪Y : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u}}
  {f : Y ⟶ X}
  (φ : ringCatSheaf 𝒪X ⟶
    ((Opens.map f).sheafPushforwardContinuous RingCat.{u} _ _).obj (ringCatSheaf 𝒪Y))
  [(pushforward.{u} φ).IsRightAdjoint]

variable {Z : TopCat.{u}} {𝒪Z : Sheaf (Opens.grothendieckTopology Z) CommRingCat.{u}}
  {g : Z ⟶ Y}
  (ψ : ringCatSheaf 𝒪Y ⟶
    ((Opens.map g).sheafPushforwardContinuous RingCat.{u} _ _).obj (ringCatSheaf 𝒪Z))
  [(pushforward.{u} ψ).IsRightAdjoint]

/-- Pullback along the composite site functor has the braided structure of pullback
along the composite map of spaces. -/
instance (priority := 100) _root_.SheafOfModules.pullbackCompBraided :
    (pullback.{u} (F := Opens.map f ⋙ Opens.map g) (R := ringCatSheaf 𝒪Z)
      (φ ≫ ((Opens.map f).sheafPushforwardContinuous RingCat.{u} _ _).map ψ)).Braided := by
  haveI : (pushforward.{u} (F := Opens.map (g ≫ f))
      (S := ringCatSheaf 𝒪X) (R := ringCatSheaf 𝒪Z)
      (φ ≫ ((Opens.map f).sheafPushforwardContinuous RingCat.{u} _ _).map ψ)).IsRightAdjoint :=
    Functor.isRightAdjoint_of_iso (pushforwardComp.{u} φ ψ)
  exact pullbackBraided (𝒪X := 𝒪X) (𝒪Y := 𝒪Z) (f := g ≫ f)
    (φ ≫ ((Opens.map f).sheafPushforwardContinuous RingCat.{u} _ _).map ψ)

/-- The canonical comparison from iterated pullback to pullback along the composite is
monoidal. -/
instance isMonoidal_pullbackComp_hom :
    NatTrans.IsMonoidal (pullbackComp.{u} φ ψ).hom := by
  let G := pullback.{u} (F := Opens.map f ⋙ Opens.map g) (R := ringCatSheaf 𝒪Z)
    (φ ≫ ((Opens.map f).sheafPushforwardContinuous RingCat.{u} _ _).map ψ)
  let e := pullbackComp.{u} φ ψ
  have hη : e.hom.app (𝟙_ _) ≫ η G = η (pullback.{u} φ ⋙ pullback.{u} ψ) := by
    dsimp only [G]
    rw [pullback_comp_η φ ψ]
    simp only [e, Iso.hom_inv_id_app_assoc, Functor.OplaxMonoidal.comp_η]
  have hδ (M N) : e.hom.app (M ⊗ N) ≫ δ G M N =
      δ (pullback.{u} φ ⋙ pullback.{u} ψ) M N ≫ (e.hom.app M ⊗ₘ e.hom.app N) := by
    dsimp only [G]
    rw [pullback_comp_δ φ ψ M N]
    simp only [e, Iso.hom_inv_id_app_assoc, Functor.OplaxMonoidal.comp_δ, Category.assoc]
  exact NatTrans.IsMonoidal.of_oplax e.hom hη hδ

end

end TauCeti.SheafOfModules
