/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Sites.Over
public import TauCeti.CategoryTheory.Sites.Pullback

/-!
# Restriction of abelian sheaves to a localized site

Restriction to `J.over U` is additive and preserves injective objects when its left adjoint,
extension to the ambient site, preserves finite limits.
-/

public section

open CategoryTheory Limits

universe u v

namespace CategoryTheory.GrothendieckTopology

/-- Restriction of abelian sheaves to the localized site `J.over U` is additive. -/
instance {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (U : C) :
    (J.overPullback AddCommGrpCat.{v} U).Additive where
  map_add := rfl

/-- Restriction of abelian sheaves to the localized site `J.over U` preserves injective objects
when its left adjoint, extension to the ambient site, preserves finite limits. -/
instance preservesInjectiveObjects_overPullback {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (U : C) [(J.overPullback AddCommGrpCat.{v} U).IsRightAdjoint]
    [PreservesFiniteLimits ((Over.forget U).sheafPullback AddCommGrpCat.{v} (J.over U) J)] :
    (J.overPullback AddCommGrpCat.{v} U).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    ((Over.forget U).sheafAdjunctionContinuous AddCommGrpCat.{v} (J.over U) J)

end CategoryTheory.GrothendieckTopology
