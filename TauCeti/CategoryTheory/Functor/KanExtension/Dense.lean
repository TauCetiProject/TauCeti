/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.Dense
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves

/-!
# Left Kan extensions along dense functors

If `F : C ⥤ D` is dense and `G : D ⥤ E` preserves the left Kan extension of `F` along itself
(for instance, when `G` preserves the canonical colimits computing the density of `F`), then `G`
is the left Kan extension of `F ⋙ G` along `F` via `𝟙 (F ⋙ G)`.
-/

public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor.IsDense

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]

/-- If `F : C ⥤ D` is dense and `G : D ⥤ E` preserves the left Kan extension of `F` along itself
(in particular, when `G` preserves colimits of the canonical density diagrams), then `G` is the
left Kan extension of `F ⋙ G` along `F` via `𝟙 (F ⋙ G)`. -/
lemma isLeftKanExtension_id (F : C ⥤ D) [F.IsDense] (G : D ⥤ E)
    [G.PreservesLeftKanExtension F F] :
    G.IsLeftKanExtension (𝟙 (F ⋙ G)) := by
  have := PreservesLeftKanExtension.preserves (G := G) (𝟭 D) (Functor.rightUnitor F).inv
  exact isLeftKanExtension_of_iso (Functor.leftUnitor G)
    (whiskerRight (Functor.rightUnitor F).inv G ≫ (Functor.associator F (𝟭 D) G).hom)
    (𝟙 (F ⋙ G)) (by ext m; simp)

end CategoryTheory.Functor.IsDense
