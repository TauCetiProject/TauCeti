/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Descent.Banding.Stackification
import TauCeti.CategoryTheory.Sites.Descent.RelativeGerbe

/-!
# Checks for descent of abelian bandings

These checks use the independent site and fibre universes needed by a big scheme site.
They verify descent along the identity and the formula on an object in the image of the
stackification unit.
-/

public section

noncomputable section

universe u

open CategoryTheory Opposite Bicategory Pseudofunctor

namespace TauCeti.Examples.BandingStackification

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
  {A : Sheaf J AddCommGrpCat.{u}}
  {F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{u, u + 1}}

local instance : (StrongTrans.id F).IsLocallyEssSurj J :=
  StrongTrans.isLocallyEssSurj_of_essSurj _ fun _ ↦ by
    dsimp [StrongTrans.id]
    infer_instance

example [F.IsPrestack J] (b : F.AbelianBanding J A) :
    b.descend (StrongTrans.id F) (fun _ ↦ .id _) = b := by
  let := b.bandPreserving_descend (StrongTrans.id F) (fun _ ↦ .id _)
  exact b.eq_of_bandPreserving (StrongTrans.id F)
    (b.descend (StrongTrans.id F) (fun _ ↦ .id _)) b

example [G.IsPrestack J] (b : F.AbelianBanding J A) (η : StrongTrans F G)
    (hη : ∀ U : C, (η.app (.mk (op U))).toFunctor.FullyFaithful)
    [η.IsLocallyEssSurj J] : ∃! bG : G.AbelianBanding J A, BandPreserving b bG η :=
  b.existsUnique_bandPreserving η hη

variable [Limits.HasPullbacks C] [F.IsPrestack J]

example (b : F.AbelianBanding J A) (U : C) (x : F.obj (.mk (op U)))
    (a : Multiplicative (A.obj.obj (op U))) :
    (b.stackification.{u, u, u + 1, u, u + 1, u}).mulEquiv U
        (((Stack.toStackification.{u, u, u + 1} J F).app (.mk (op U))).toFunctor.obj x) a =
      ((Stack.toStackification.{u, u, u + 1} J F).app (.mk (op U))).toFunctor.mapAut x
        (b.mulEquiv U x a) :=
  b.stackification_mulEquiv_image U x a

end TauCeti.Examples.BandingStackification
