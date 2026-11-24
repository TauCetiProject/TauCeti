/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Generator.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

/-!
# Morphisms out of the summands of a separator

In a category with zero morphisms, every nonzero object receives a nonzero morphism from a member
of a separating family (`CategoryTheory.ObjectProperty.IsSeparating.exists_hom_ne_zero`). So if a
separator `G` is a coproduct of objects `P j`, then every nonzero object receives a nonzero
morphism from one of the summands `P j`
(`CategoryTheory.IsSeparator.exists_hom_ne_zero_of_isColimit_cofan`), in particular when `G` is a
biproduct (`CategoryTheory.IsSeparator.exists_hom_ne_zero_of_iso_biproduct`). For the regular
module (`ModuleCat.isSeparator`) of a left Artinian ring decomposed into indecomposables, these
summands are the indecomposable projective modules.
-/

public section

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

/-- **Every nonzero object receives a nonzero morphism from a separating family.** -/
theorem ObjectProperty.IsSeparating.exists_hom_ne_zero {P : ObjectProperty C}
    (hP : P.IsSeparating) {M : C} (hM : ¬ IsZero M) : ∃ (G : C) (_ : P G) (f : G ⟶ M), f ≠ 0 := by
  -- Otherwise `𝟙 M` and `0` agree after every morphism from the family.
  by_contra! h
  exact hM ((IsZero.iff_id_eq_zero M).mpr
    (hP _ _ fun G hG t ↦ by rw [h G hG t, zero_comp, zero_comp]))

namespace IsSeparator

/-- **Every nonzero object receives a nonzero morphism from a summand of a separator.** If a
separator `G` is a coproduct of objects `P j`, then every nonzero object `M` admits a nonzero
morphism `P j ⟶ M` for some `j`. -/
theorem exists_hom_ne_zero_of_isColimit_cofan {G : C} (hG : IsSeparator G) {J : Type*}
    {P : J → C} {c : Cofan P} (hc : IsColimit c) (e : G ≅ c.pt) {M : C} (hM : ¬ IsZero M) :
    ∃ (j : J) (f : P j ⟶ M), f ≠ 0 := by
  -- The summands form a separating family, since `c.pt ≅ G` is a separator.
  have hP : ObjectProperty.IsSeparating (.ofObj P) :=
    (isSeparator_iff_of_isColimit_cofan hc).mp <| (isSeparator_def _).mpr fun _ _ f g h ↦
      hG.def f g fun t ↦ by simpa using e.hom ≫= h (e.inv ≫ t)
  obtain ⟨_, ⟨j⟩, f, hf⟩ := hP.exists_hom_ne_zero hM
  exact ⟨j, f, hf⟩

/-- **Every nonzero object receives a nonzero morphism from a summand of a separator.** If a
separator `G` is a biproduct of objects `P j`, then every nonzero object `M` admits a nonzero
morphism `P j ⟶ M` for some `j`. -/
theorem exists_hom_ne_zero_of_iso_biproduct {G : C} (hG : IsSeparator G) {J : Type*}
    {P : J → C} [HasBiproduct P] (e : G ≅ ⨁ P) {M : C} (hM : ¬ IsZero M) :
    ∃ (j : J) (f : P j ⟶ M), f ≠ 0 :=
  hG.exists_hom_ne_zero_of_isColimit_cofan (biproduct.isColimit P) e hM

end IsSeparator

end CategoryTheory
