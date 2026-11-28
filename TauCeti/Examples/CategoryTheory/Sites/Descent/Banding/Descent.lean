/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Descent.Banding.Descent

/-!
# Checks for descent of abelian bandings

These checks use the independent site and fibre universes needed by a big scheme site.
They verify descent along the identity and uniqueness without importing stackification.
-/

public section

noncomputable section

universe u

open CategoryTheory Opposite Bicategory Pseudofunctor

namespace TauCeti.Examples.BandingDescent

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
  {A : Sheaf J AddCommGrpCat.{u}}
  {F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{u, u + 1}}

local instance : (StrongTrans.id F).IsLocallyEssSurj J :=
  StrongTrans.isLocallyEssSurj_of_essSurj _ fun _ ↦ by
    dsimp only [StrongTrans.id, Cat.Hom.id_toFunctor]
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

end TauCeti.Examples.BandingDescent
