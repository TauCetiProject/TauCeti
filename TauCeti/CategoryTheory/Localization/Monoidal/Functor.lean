/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Localization.Monoidal.Functor
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Braided universal property of localized monoidal categories

Let `L : C ⥤ D` be a braided monoidal localization functor for `W`, and let `F : D ⥤ E` lift a
braided monoidal functor `G : C ⥤ E` along `L`. Mathlib's
`CategoryTheory.Localization.Monoidal.functorMonoidalOfComp` equips `F` with a strong monoidal
structure making the lifting isomorphism `L ⋙ F ≅ G` monoidal. This file upgrades that structure
to a braided monoidal structure (`CategoryTheory.Localization.Monoidal.functorBraidedOfComp`).
-/

public section

open CategoryTheory MonoidalCategory BraidedCategory
open CategoryTheory.Functor LaxMonoidal OplaxMonoidal

namespace CategoryTheory.Localization.Monoidal

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
  [BraidedCategory C] [BraidedCategory D] [BraidedCategory E]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] [L.Braided]
  (F : D ⥤ E) (G : C ⥤ E) [G.Braided] [W.ContainsIdentities] [Lifting L W G F]

/-- When `L : C ⥤ D` is a braided monoidal localization functor and `F : D ⥤ E` lifts a braided
monoidal functor `G : C ⥤ E` along `L`, the monoidal structure `functorMonoidalOfComp L W F G`
on `F` respects the braiding. -/
theorem curriedTensorPreIsoPost_braiding (M N : D) :
    ((curriedTensorPreIsoPost L W F G).hom.app M).app N ≫ F.map (β_ M N).hom =
      (β_ (F.obj M) (F.obj N)).hom ≫
        ((curriedTensorPreIsoPost L W F G).hom.app N).app M := by
  have := Localization.essSurj L W
  let X := L.objPreimage M
  let Y := L.objPreimage N
  let eM : M ≅ L.obj X := (L.objObjPreimageIso M).symm
  let eN : N ≅ L.obj Y := (L.objObjPreimageIso N).symm
  have hδ : δ L X Y ≫ (β_ (L.obj X) (L.obj Y)).hom = L.map (β_ X Y).hom ≫ δ L Y X := by
    rw [← cancel_epi (μ L X Y), Functor.Monoidal.μ_δ_assoc,
      Functor.LaxBraided.braided_assoc, Functor.Monoidal.μ_δ, Category.comp_id]
  rw [curriedTensorPreIsoPost_hom_app_app' L W F G eM eN,
    curriedTensorPreIsoPost_hom_app_app' L W F G eN eM]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [BraidedCategory.braiding_naturality, reassoc_of% hδ, Functor.map_comp,
    ← reassoc_of% (Lifting.iso L W G F).inv.naturality (β_ X Y).hom,
    reassoc_of% (Functor.LaxBraided.braided (F := G) X Y),
    reassoc_of% (BraidedCategory.braiding_naturality
      (F.map eM.hom ≫ (Lifting.iso L W G F).hom.app X)
      (F.map eN.hom ≫ (Lifting.iso L W G F).hom.app Y))]

/-- Braided monoidal structure on `F`, given that `F` lifts a braided monoidal functor `G` along a
braided monoidal localization functor `L`. Its underlying monoidal structure is
`functorMonoidalOfComp L W F G`. -/
@[expose, instance_reducible]
noncomputable def functorBraidedOfComp : F.Braided :=
  letI : F.Monoidal := functorMonoidalOfComp L W F G
  { toMonoidal := functorMonoidalOfComp L W F G
    braided M N := curriedTensorPreIsoPost_braiding L W F G M N }

/-- The underlying strong monoidal structure of `functorBraidedOfComp` is
`functorMonoidalOfComp`. -/
@[simp]
theorem functorBraidedOfComp_toMonoidal :
    (functorBraidedOfComp L W F G).toMonoidal = functorMonoidalOfComp L W F G :=
  (rfl)

end CategoryTheory.Localization.Monoidal
