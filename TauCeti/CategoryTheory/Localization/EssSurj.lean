/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Essential surjectivity of localizations restricted to a class of objects

Let `L : C ⥤ D` be a localization with respect to a class of morphisms `W`, and `Q` a class of
objects of `C`. If every object `X` has a morphism `X ⟶ Y` in `W` with `Y` in `Q` (a resolution
by `Q`), then the restriction `Q.ι ⋙ L` is essentially surjective: every object of `D` is
isomorphic to `L.obj X` for some `X`, and `L.obj X ≅ L.obj Y` since `L` inverts `W`. The same
holds with morphisms `Y ⟶ X` in `W`.

Together with fully faithfulness, this shows that resolutions by a suitable class compute a
localization, as for derived categories computed by complexes of injectives or projectives.

## Main results

* `CategoryTheory.ObjectProperty.essSurj_ι_comp_of_exists_to`: resolutions through morphisms in
  `W` out of each object.
* `CategoryTheory.ObjectProperty.essSurj_ι_comp_of_exists_from`: resolutions through morphisms in
  `W` into each object.
-/

public section

namespace CategoryTheory.ObjectProperty

variable {C D : Type*} [Category* C] [Category* D] (W : MorphismProperty C) (L : C ⥤ D)
  [L.IsLocalization W] {Q : ObjectProperty C}

/-- If every object has a morphism in `W` to an object of `Q`, then `Q.ι ⋙ L` is essentially
surjective for a localization `L` with respect to `W`. -/
theorem essSurj_ι_comp_of_exists_to
    (hs : ∀ X : C, ∃ (Y : C) (s : X ⟶ Y), Q Y ∧ W s) : (Q.ι ⋙ L).EssSurj where
  mem_essImage Z := by
    obtain ⟨X, ⟨e⟩⟩ := (Localization.essSurj L W).mem_essImage Z
    obtain ⟨Y, s, hY, hs⟩ := hs X
    have := Localization.inverts L W s hs
    exact ⟨⟨Y, hY⟩, ⟨(asIso (L.map s)).symm ≪≫ e⟩⟩

/-- If every object has a morphism in `W` from an object of `Q`, then `Q.ι ⋙ L` is essentially
surjective for a localization `L` with respect to `W`. -/
theorem essSurj_ι_comp_of_exists_from
    (hs : ∀ X : C, ∃ (Y : C) (s : Y ⟶ X), Q Y ∧ W s) : (Q.ι ⋙ L).EssSurj where
  mem_essImage Z := by
    obtain ⟨X, ⟨e⟩⟩ := (Localization.essSurj L W).mem_essImage Z
    obtain ⟨Y, s, hY, hs⟩ := hs X
    have := Localization.inverts L W s hs
    exact ⟨⟨Y, hY⟩, ⟨asIso (L.map s) ≪≫ e⟩⟩

end CategoryTheory.ObjectProperty
