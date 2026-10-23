/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.Equivalence

/-!
# Equivalences onto the essential image with a prescribed inverse

A fully faithful functor `L : C ⥤ D` is an equivalence onto its essential image
(`CategoryTheory.Functor.fullyFaithfulToEssImage`), but the inverse of `L.toEssImage.asEquivalence`
is chosen. When `L` is full and admits a retraction `R : D ⥤ C`, in the sense of a natural
isomorphism `e : L ⋙ R ≅ 𝟭 C` (which makes `L` faithful), this file constructs the equivalence
`C ≌ L.EssImageSubcategory` whose inverse is `R` restricted to the essential image and whose unit
is `e.symm`. Its counit is determined by the triangle identities; on objects `L.obj X` it is
`L.map (e.hom.app X)`, by `CategoryTheory.Equivalence.counit_app_functor`.

This is the shape of the equivalence between a category of coefficients and the free objects on
them, whose coefficients are recovered by a retraction: for instance, quasicoherent sheaves and
their graded symmetric algebras, with the degree-one component as retraction.

## Main declarations

* `CategoryTheory.Functor.equivEssImageOfCompIso`: the equivalence onto the essential image with
  inverse `L.essImage.ι ⋙ R` and unit `e.symm`.
-/

public section

namespace CategoryTheory

namespace Functor

variable {C D : Type*} [Category* C] [Category* D] (L : C ⥤ D) [L.Full] {R : D ⥤ C}
  (e : L ⋙ R ≅ 𝟭 C)

/-- A full functor `L` with a retraction `e : L ⋙ R ≅ 𝟭 C`, which is then fully faithful, is an
equivalence onto its essential image whose inverse is `R` restricted to the essential image and
whose unit is `e.symm`. -/
-- Exposed so that the unit `e.symm` can be stated as an isomorphism of the functors `L ⋙ R` and
-- `𝟭 C`, which are the composite and the identity of the equivalence only by unfolding it.
@[expose]
noncomputable def equivEssImageOfCompIso : C ≌ L.EssImageSubcategory :=
  haveI : L.Faithful := Faithful.of_comp_iso e
  -- The chosen inverse of `L.toEssImage` is replaced by `L.essImage.ι ⋙ R`, through the
  -- isomorphism `inverse ≅ inverse ⋙ L ⋙ R ≅ (inverse ⋙ L.toEssImage) ⋙ ι ⋙ R ≅ ι ⋙ R`.
  let E := L.toEssImage.asEquivalence.changeInverse ((Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft L.toEssImage.asEquivalence.inverse
      (e.symm ≪≫ Functor.isoWhiskerRight L.toEssImageCompι.symm R ≪≫
        Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight L.toEssImage.asEquivalence.counitIso _ ≪≫ Functor.leftUnitor _)
  { functor := L.toEssImage
    inverse := L.essImage.ι ⋙ R
    unitIso := e.symm
    counitIso := E.counitIso
    functor_unitIso_comp X := by
      -- The unit of `E` is `e.symm`: by naturality of `e.inv` it is `e.inv.app X` followed by
      -- `R` applied to the triangle identity of `L.toEssImage.asEquivalence` at `X`.
      have h := congrArg (fun f ↦ R.map f.hom) (L.toEssImage.asEquivalence.functor_unit_comp X)
      have hn := e.inv.naturality (L.toEssImage.asEquivalence.unitIso.hom.app X)
      simp only [Equivalence.unit, Equivalence.counit, Functor.asEquivalence_functor,
        ObjectProperty.FullSubcategory.comp_hom, toEssImage_map_hom, Functor.map_comp,
        ObjectProperty.FullSubcategory.id_hom, Functor.map_id] at h
      simp only [Functor.id_map, Functor.comp_map, Functor.asEquivalence_functor] at hn
      have hu : E.unitIso.hom.app X = e.inv.app X := by
        simp [E, Equivalence.changeInverse, reassoc_of% hn, h]
      have h' := E.functor_unit_comp X
      rw [hu] at h'
      exact h' }

/-- The forward functor of `equivEssImageOfCompIso` is the corestriction of `L` to its essential
image. -/
@[simp]
theorem equivEssImageOfCompIso_functor : (L.equivEssImageOfCompIso e).functor = L.toEssImage :=
  (rfl)

/-- The inverse functor of `equivEssImageOfCompIso` is the retraction `R` restricted to the
essential image. -/
@[simp]
theorem equivEssImageOfCompIso_inverse :
    (L.equivEssImageOfCompIso e).inverse = L.essImage.ι ⋙ R :=
  (rfl)

/-- The unit of `equivEssImageOfCompIso` is the inverse of the retraction isomorphism. -/
@[simp]
theorem equivEssImageOfCompIso_unitIso : (L.equivEssImageOfCompIso e).unitIso = e.symm :=
  (rfl)

end Functor

end CategoryTheory
