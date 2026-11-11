/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Triangulated.Orthogonal
public import TauCeti.CategoryTheory.Localization.EssSurj

/-!
# Verdier quotients computed by orthogonal subcategories

Let `P` be a triangulated subcategory of a triangulated category `C`, and `L : C ⥤ D` a
localization with respect to `P.trW`, for instance the Verdier quotient `C / P`. Let `Q` be a
class of objects right orthogonal to `P`: no nonzero morphisms from `P` to `Q`. Mathlib's
`CategoryTheory.ObjectProperty.rightOrthogonal.map_bijective_of_isTriangulated` shows that `L` is
bijective on morphisms into objects of `Q`, so the restriction `Q.ι ⋙ L` is fully faithful. If
moreover every object `X` has a morphism `X ⟶ Y` in `P.trW` with `Y` in `Q` (a resolution by `Q`),
then `Q.ι ⋙ L` is essentially surjective, by the general
`CategoryTheory.ObjectProperty.essSurj_ι_comp_of_exists_to`, hence an equivalence `Q ≌ D`.

The dual statement holds for left orthogonal classes with morphisms `Y ⟶ X` in `P.trW`.

Typical instances: bounded below complexes of injectives compute the bounded below derived category
of an exact category with enough injectives, and K-projective or K-injective complexes compute
unbounded derived categories.

## Main results

* `CategoryTheory.ObjectProperty.isEquivalence_ι_comp_of_le_rightOrthogonal`: resolutions by a right
  orthogonal class give an equivalence with the localization.
* `CategoryTheory.ObjectProperty.isEquivalence_ι_comp_of_le_leftOrthogonal`: the dual statement.

## References

* Mathlib's `CategoryTheory.ObjectProperty.rightOrthogonal.map_bijective_of_isTriangulated` and
  `CategoryTheory.ObjectProperty.leftOrthogonal.map_bijective_of_isTriangulated`, which give the
  fully faithfulness.
-/

public section

namespace CategoryTheory.ObjectProperty

open Limits Pretriangulated

variable {C D : Type*} [Category* C] [Category* D] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
  {P : ObjectProperty C} [P.IsTriangulated] (L : C ⥤ D) [L.IsLocalization P.trW]
  {Q : ObjectProperty C}

/-- A localization with respect to `P.trW` is full on a class of objects right orthogonal to
`P`. -/
theorem full_ι_comp_of_le_rightOrthogonal (hQ : Q ≤ P.rightOrthogonal) : (Q.ι ⋙ L).Full where
  map_surjective {X Y} g := by
    obtain ⟨f, hf⟩ := ((hQ _ Y.property).map_bijective_of_isTriangulated L X.obj).surjective g
    exact ⟨ObjectProperty.homMk f, hf⟩

/-- A localization with respect to `P.trW` is faithful on a class of objects right orthogonal to
`P`. -/
theorem faithful_ι_comp_of_le_rightOrthogonal (hQ : Q ≤ P.rightOrthogonal) :
    (Q.ι ⋙ L).Faithful where
  map_injective {X Y} _ _ h :=
    ObjectProperty.hom_ext _
      (((hQ _ Y.property).map_bijective_of_isTriangulated L X.obj).injective h)

/-- **Resolutions by a right orthogonal class compute the localization**: if `Q` is right
orthogonal to `P` and every object has a morphism in `P.trW` to an object of `Q`, then
`Q.ι ⋙ L` is an equivalence. -/
theorem isEquivalence_ι_comp_of_le_rightOrthogonal (hQ : Q ≤ P.rightOrthogonal)
    (hs : ∀ X : C, ∃ (Y : C) (s : X ⟶ Y), Q Y ∧ P.trW s) : (Q.ι ⋙ L).IsEquivalence where
  faithful := faithful_ι_comp_of_le_rightOrthogonal L hQ
  full := full_ι_comp_of_le_rightOrthogonal L hQ
  essSurj := essSurj_ι_comp_of_exists_to P.trW L hs

/-- A localization with respect to `P.trW` is full on a class of objects left orthogonal to
`P`. -/
theorem full_ι_comp_of_le_leftOrthogonal (hQ : Q ≤ P.leftOrthogonal) : (Q.ι ⋙ L).Full where
  map_surjective {X Y} g := by
    obtain ⟨f, hf⟩ := ((hQ _ X.property).map_bijective_of_isTriangulated L Y.obj).surjective g
    exact ⟨ObjectProperty.homMk f, hf⟩

/-- A localization with respect to `P.trW` is faithful on a class of objects left orthogonal to
`P`. -/
theorem faithful_ι_comp_of_le_leftOrthogonal (hQ : Q ≤ P.leftOrthogonal) :
    (Q.ι ⋙ L).Faithful where
  map_injective {X Y} _ _ h :=
    ObjectProperty.hom_ext _
      (((hQ _ X.property).map_bijective_of_isTriangulated L Y.obj).injective h)

/-- **Resolutions by a left orthogonal class compute the localization**: if `Q` is left
orthogonal to `P` and every object has a morphism in `P.trW` from an object of `Q`, then
`Q.ι ⋙ L` is an equivalence. -/
theorem isEquivalence_ι_comp_of_le_leftOrthogonal (hQ : Q ≤ P.leftOrthogonal)
    (hs : ∀ X : C, ∃ (Y : C) (s : Y ⟶ X), Q Y ∧ P.trW s) : (Q.ι ⋙ L).IsEquivalence where
  faithful := faithful_ι_comp_of_le_leftOrthogonal L hQ
  full := full_ι_comp_of_le_leftOrthogonal L hQ
  essSurj := essSurj_ι_comp_of_exists_from P.trW L hs

end CategoryTheory.ObjectProperty
