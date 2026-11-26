/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Natural transformations at preserved cokernels

Let `τ : F ⟶ G` be a natural transformation between functors which preserve zero morphisms, let
`c` be a cokernel cofork of `f : X ⟶ Y`, and suppose that `G` preserves this cokernel while `F`
sends the projection `c.π` to an epimorphism. If `τ` is an epimorphism at `X` and an isomorphism
at `Y`, then it is an isomorphism at `c.pt`
(`CategoryTheory.NatTrans.isIso_app_of_isColimit_cokernelCofork`). This is a four lemma for the
rows `F X ⟶ F Y ⟶ F c.pt ⟶ 0` and `G X ⟶ G Y ⟶ G c.pt ⟶ 0`, where only the second row needs to be
right exact. It is proved directly from the universal property of the cokernel in the second row,
so no abelian structure is needed.
-/

public section

open CategoryTheory Limits

namespace CategoryTheory.NatTrans

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]
  {F G : C ⥤ D} [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] (τ : F ⟶ G)

/-- Let `c` be a cokernel cofork of `f : X ⟶ Y` which `G` preserves, and suppose `F` sends its
projection to an epimorphism. A natural transformation `τ : F ⟶ G` which is an epimorphism at `X`
and an isomorphism at `Y` is an isomorphism at `c.pt`. -/
theorem isIso_app_of_isColimit_cokernelCofork {X Y : C} {f : X ⟶ Y} {c : CokernelCofork f}
    (hc : IsColimit c) [PreservesColimit (parallelPair f 0) G] [Epi (F.map c.π)]
    [Epi (τ.app X)] [IsIso (τ.app Y)] :
    IsIso (τ.app c.pt) := by
  have hG := CokernelCofork.mapIsColimit c hc G
  have w : G.map f ≫ inv (τ.app Y) ≫ F.map c.π = 0 := by
    rw [← cancel_epi (τ.app X), comp_zero, ← τ.naturality_assoc, IsIso.hom_inv_id_assoc,
      ← F.map_comp, CokernelCofork.condition, F.map_zero]
  obtain ⟨g, hg⟩ := CokernelCofork.IsColimit.desc' hG _ w
  -- `hg` says that `G.map c.π ≫ g = inv (τ.app Y) ≫ F.map c.π`.
  rw [CokernelCofork.map_π] at hg
  refine ⟨g, (cancel_epi (F.map c.π)).mp ?_, Cofork.IsColimit.hom_ext hG ?_⟩
  · rw [τ.naturality_assoc, hg, IsIso.hom_inv_id_assoc, Category.comp_id]
  · rw [CokernelCofork.map_π, reassoc_of% hg, τ.naturality, IsIso.inv_hom_id_assoc]
    exact (Category.comp_id _).symm

end CategoryTheory.NatTrans
