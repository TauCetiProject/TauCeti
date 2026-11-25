/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic

/-!
# Categorical pullbacks of groupoids

For functors `F : A ⥤ B` and `G : C ⥤ B`, a morphism of the categorical pullback `F ⊡ G` is an
isomorphism exactly when both of its components are (`CategoricalPullback.isIso_iff`). Hence the
categorical pullback of two groupoids over any category is a groupoid. This is what makes a
2-fibre product of stacks in groupoids again have groupoid fibres.

## Main declarations

* `CategoryTheory.Limits.CategoricalPullback.isGroupoid`: `F ⊡ G` is a groupoid when `A` and `C`
  are.
-/

public section

namespace CategoryTheory.Limits.CategoricalPullback

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]

/-- The categorical pullback of two groupoids over any category is a groupoid. -/
instance isGroupoid [IsGroupoid A] [IsGroupoid C] (F : A ⥤ B) (G : C ⥤ B) :
    IsGroupoid (F ⊡ G) where
  all_isIso u := (isIso_iff F G u).mpr ⟨inferInstance, inferInstance⟩

end CategoryTheory.Limits.CategoricalPullback
