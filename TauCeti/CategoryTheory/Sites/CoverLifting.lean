/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.CoverLifting

/-!
# Sheafification of a comparison into a restricted presheaf

Let `G : C ⥤ D` be continuous and cocontinuous for topologies `J` on `C` and `K` on `D`, so that
restriction along `G` commutes with sheafification
(`Functor.pushforwardContinuousSheafificationCompatibility`). A morphism of presheaves
`e : P ⟶ G.op ⋙ Q` then sheafifies to a morphism from the sheafification of `P` to the
restriction of the sheafification of `Q`, and this sheafified comparison is compatible with the
canonical maps of `P` and `Q` into their sheafifications.

## Main results

* `CategoryTheory.Functor.toSheafify_comp_sheafifyMap_comp_sheafificationCompatibility_hom`: the
  canonical map of `P` followed by the sheafified comparison is `e` followed by the restriction of
  the canonical map of `Q`.
-/

public section

open CategoryTheory

namespace CategoryTheory.Functor

variable {C : Type*} [Category* C] {D : Type*} [Category* D] (G : C ⥤ D)
  (A : Type*) [Category* A] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [G.IsContinuous J K] [G.IsCocontinuous J K]
  [∀ (F : Cᵒᵖ ⥤ A), G.op.HasPointwiseRightKanExtension F]
  [HasWeakSheafify J A] [HasWeakSheafify K A]

/-- Sheafifying a comparison `e : P ⟶ G.op ⋙ Q` and composing with the compatibility of
restriction along `G` with sheafification sends the canonical map of `P` into its sheafification
to `e` followed by the restriction of the canonical map of `Q`. -/
@[reassoc]
lemma toSheafify_comp_sheafifyMap_comp_sheafificationCompatibility_hom {P : Cᵒᵖ ⥤ A}
    {Q : Dᵒᵖ ⥤ A} (e : P ⟶ G.op ⋙ Q) :
    toSheafify J P ≫ sheafifyMap J e ≫
        ((G.pushforwardContinuousSheafificationCompatibility A J K).hom.app Q).hom =
      e ≫ whiskerLeft G.op (toSheafify K Q) := by
  rw [← reassoc_of% toSheafify_naturality]
  exact e ≫= G.toSheafify_pullbackSheafificationCompatibility A J K Q

end CategoryTheory.Functor
