/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Descent.Banding.Stackification

/-!
# Checks for descent of abelian bandings

These checks use the independent site and fibre universes needed by a big scheme site.
They verify the unit formula and simplification of band preservation for maps and lifts.
-/

public section

noncomputable section

universe u

open CategoryTheory Opposite Bicategory Pseudofunctor

namespace TauCeti.Examples.BandingStackification

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
  {A : Sheaf J AddCommGrpCat.{u}}
  {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{u, u + 1}}

variable [Limits.HasPullbacks C] [F.IsPrestack J]

example (b : F.AbelianBanding J A) (U : C) (x : F.obj (.mk (op U)))
    (a : Multiplicative (A.obj.obj (op U))) :
    (b.stackification.{u, u, u + 1, u, u + 1, u}).mulEquiv U
        (((Stack.toStackification.{u, u, u + 1} J F).app (.mk (op U))).toFunctor.obj x) a =
      ((Stack.toStackification.{u, u, u + 1} J F).app (.mk (op U))).toFunctor.mapAut x
        (b.mulEquiv U x a) :=
  b.stackification_mulEquiv_obj U x a

variable {G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{u, u + 1}}

example [G.IsPrestack J] (b : F.AbelianBanding J A) (bG : G.AbelianBanding J A)
    (ψ : StrongTrans F G) :
    BandPreserving (b.stackification.{u, u, u + 1, u, u + 1, u})
      (bG.stackification.{u, u, u + 1, u, u + 1, u}) (Stack.stackificationMap.{u} J ψ) ↔
      BandPreserving b bG ψ := by
  simp

example [G.IsStack J] (b : F.AbelianBanding J A) (bG : G.AbelianBanding J A)
    (ψ : StrongTrans F G) :
    BandPreserving (b.stackification.{u, u, u + 1, u, u + 1, u}) bG
      (Stack.stackificationLift.{u, u, u + 1} J ψ) ↔ BandPreserving b bG ψ := by
  simp

end TauCeti.Examples.BandingStackification
