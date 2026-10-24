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
  inverse `L.essImage.ι ⋙ R` and unit `e.symm`;
* `CategoryTheory.Functor.essImage_iff_nonempty_iso_of_compIso`: an object `A` lies in the
  essential image of `L` exactly when `L.obj (R.obj A) ≅ A`.
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
  -- `Equivalence.mk` keeps its counit `e` and adjusts its unit, so the unit of the symmetric
  -- equivalence is `e.symm`.
  (Equivalence.mk (L.essImage.ι ⋙ R) L.toEssImage E.counitIso.symm e).symm

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

include e in
omit [L.Full] in
/-- An object lies in the essential image of a functor `L` with a retraction `e : L ⋙ R ≅ 𝟭 C`
exactly when it is isomorphic to `L` applied to its image under `R`. -/
theorem essImage_iff_nonempty_iso_of_compIso (A : D) :
    L.essImage A ↔ Nonempty (L.obj (R.obj A) ≅ A) :=
  ⟨fun ⟨X, ⟨i⟩⟩ ↦ ⟨L.mapIso (R.mapIso i.symm ≪≫ e.app X) ≪≫ i⟩, fun ⟨i⟩ ↦ ⟨_, ⟨i⟩⟩⟩

end Functor

end CategoryTheory
