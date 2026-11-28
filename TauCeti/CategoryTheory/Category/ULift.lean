/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Category.ULift

/-!
# Strict functorial round-trips for `CategoryTheory.AsSmall`

Mathlib's `CategoryTheory.AsSmall.equiv : C ≌ AsSmall.{w} C` supplies natural isomorphisms
`AsSmall.up ⋙ AsSmall.down ≅ 𝟭 C` and `AsSmall.down ⋙ AsSmall.up ≅ 𝟭 (AsSmall.{w} C)`. Since
`AsSmall.up` and `AsSmall.down` act on objects and morphisms by wrapping and unwrapping `ULift`,
both composites are in fact strictly equal to the respective identity functors
(`CategoryTheory.AsSmall.up_comp_down` and `CategoryTheory.AsSmall.down_comp_up`).
-/

public section

namespace CategoryTheory.AsSmall

universe w v u

/-- Composing `AsSmall.up : C ⥤ AsSmall.{w} C` with `AsSmall.down` is strictly the identity
functor `𝟭 C`. -/
@[simp]
theorem up_comp_down (C : Type u) [Category.{v} C] :
    (AsSmall.up : C ⥤ AsSmall.{w} C) ⋙ AsSmall.down = 𝟭 C :=
  Functor.hext (fun _ ↦ rfl) fun _ _ _ ↦ .rfl

/-- Composing `AsSmall.down : AsSmall.{w} C ⥤ C` with `AsSmall.up` is strictly the identity
functor `𝟭 (AsSmall.{w} C)`. -/
@[simp]
theorem down_comp_up (C : Type u) [Category.{v} C] :
    (AsSmall.down : AsSmall.{w} C ⥤ C) ⋙ AsSmall.up = 𝟭 (AsSmall.{w} C) :=
  Functor.hext (fun _ ↦ rfl) fun _ _ _ ↦ .rfl

end CategoryTheory.AsSmall
