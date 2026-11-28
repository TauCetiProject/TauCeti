/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Plus

/-!
# Natural transformations on the bounded below homotopy category

The comparison between mapping and including bounded below complexes is natural
in the additive functor.
-/

public section

namespace CategoryTheory.NatTrans

variable {C D : Type*} [Category* C] [Preadditive C] [Category* D] [Preadditive D]
  {F G : C ⥤ D} [F.Additive] [G.Additive]

/-- Including the induced transformation into the homotopy category recovers the usual
induced transformation, via the comparison isomorphisms. -/
@[reassoc]
lemma mapHomotopyCategoryPlusCompι_hom_app_naturality (τ : F ⟶ G)
    (K : HomotopyCategory.Plus C) :
    (HomotopyCategory.Plus.ι D).map (τ.mapHomotopyCategoryPlus.app K) ≫
        G.mapHomotopyCategoryPlusCompι.hom.app K =
      F.mapHomotopyCategoryPlusCompι.hom.app K ≫
        (τ.mapHomotopyCategory (.up ℤ)).app ((HomotopyCategory.Plus.ι C).obj K) := by
  have hτ :
      (HomotopyCategory.Plus.ι D).map (τ.mapHomotopyCategoryPlus.app K) =
        (τ.mapHomotopyCategory (.up ℤ)).app ((HomotopyCategory.Plus.ι C).obj K) := by
    simp only [ObjectProperty.ι_map, NatTrans.mapHomotopyCategoryPlus,
      ObjectProperty.homMk_hom]
  simpa only [Functor.mapHomotopyCategoryPlusCompι_hom_app, Functor.comp_obj,
    Functor.mapHomotopyCategoryPlus, ObjectProperty.ι_obj, ObjectProperty.lift_obj_obj,
    Category.comp_id, Category.id_comp] using hτ

end CategoryTheory.NatTrans
