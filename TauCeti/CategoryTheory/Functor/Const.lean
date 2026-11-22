/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.Const
public import Mathlib.CategoryTheory.Whiskering

/-!
# Whiskering with constant functors

This file supplements `Mathlib.CategoryTheory.Functor.Const` with the simplification lemma
`CategoryTheory.Functor.whiskerRight_const` showing that right-whiskering any natural
transformation `f : X ⟶ Y` between functors `J ⥤ C` by a constant functor `(const C).obj B`
equals the identity.
-/

public section

namespace CategoryTheory.Functor

universe v₁ v₂ v₃ u₁ u₂ u₃

/-- Right-whiskering any natural transformation `f : X ⟶ Y` by a constant functor
`(const C).obj B` is the identity natural transformation. -/
@[simp]
lemma whiskerRight_const {J : Type u₁} [Category.{v₁} J] {C : Type u₂} [Category.{v₂} C]
    {D : Type u₃} [Category.{v₃} D] {X Y : J ⥤ C} (f : X ⟶ Y) (B : D) :
    whiskerRight f ((const C).obj B) = 𝟙 _ := by
  ext j
  rfl

end CategoryTheory.Functor
