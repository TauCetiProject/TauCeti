/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Category.ULift

/-!
# Strict functor identities for `AsSmall`

Composing `AsSmall.up : C ⥤ AsSmall.{w} C` with `AsSmall.down` is strictly the identity functor
`𝟭 C` (`CategoryTheory.AsSmall.up_comp_down`), so conjugating a functor `F : C ⥤ D` by
`AsSmall.down` and `AsSmall.up` is strictly undone by `AsSmall.up` and `AsSmall.down`
(`CategoryTheory.AsSmall.up_comp_down_comp_up_comp_down`).
-/

public section

universe w w₁ w₂ v v₁ v₂ u u₁ u₂

namespace CategoryTheory.AsSmall

/-- Composing `AsSmall.up : C ⥤ AsSmall.{w} C` with `AsSmall.down` is strictly the identity
functor `𝟭 C`. -/
lemma up_comp_down (C : Type u) [Category.{v} C] :
    (AsSmall.up : C ⥤ AsSmall.{w} C) ⋙ AsSmall.down = 𝟭 C :=
  rfl

/-- Conjugating a functor `F : C ⥤ D` by `AsSmall.down` and `AsSmall.up` and undoing the
conjugation with `AsSmall.up` and `AsSmall.down` recovers `F`. -/
lemma up_comp_down_comp_up_comp_down {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) :
    (AsSmall.up ⋙
      (AsSmall.down (C := C) ⋙ F ⋙ AsSmall.up : AsSmall.{w₁} C ⥤ AsSmall.{w₂} D)) ⋙
      AsSmall.down = F := by
  rw [← Functor.assoc, up_comp_down, Functor.id_comp, Functor.assoc, up_comp_down, Functor.comp_id]

end CategoryTheory.AsSmall
