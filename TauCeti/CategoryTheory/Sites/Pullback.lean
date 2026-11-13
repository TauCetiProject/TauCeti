/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Pullback

/-!
# Pullback of abelian sheaves

Mathlib's `CategoryTheory.Functor.sheafPullback` is the left adjoint of the pushforward of sheaves
along a continuous functor. For sheaves of abelian groups, this file records that it is additive
and right exact, as a left adjoint between preadditive categories.

## Main declarations

* `CategoryTheory.Functor.sheafPullback_additive`: the pullback of abelian sheaves is additive.
* `CategoryTheory.Functor.preservesFiniteColimits_sheafPullback`: the pullback of abelian sheaves
  preserves finite colimits.
-/

public section

universe w

namespace CategoryTheory.Functor

open Limits

variable {C : Type*} [Category* C] {J : GrothendieckTopology C}
  {D : Type*} [Category* D] {K : GrothendieckTopology D}
  (u : C ⥤ D) [u.IsContinuous J K]
  [(u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsRightAdjoint]

/-- The pullback of abelian sheaves along a continuous functor is additive, as a left adjoint. -/
instance sheafPullback_additive : (u.sheafPullback AddCommGrpCat.{w} J K).Additive :=
  haveI : (u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).Additive :=
    Functor.additive_of_preserves_binary_products _
  (u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).left_adjoint_additive

/-- The pullback of abelian sheaves along a continuous functor preserves finite colimits, as a
left adjoint. -/
instance preservesFiniteColimits_sheafPullback :
    PreservesFiniteColimits (u.sheafPullback AddCommGrpCat.{w} J K) :=
  letI := (u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).leftAdjoint_preservesColimits.{0, 0}
  inferInstance

end CategoryTheory.Functor
