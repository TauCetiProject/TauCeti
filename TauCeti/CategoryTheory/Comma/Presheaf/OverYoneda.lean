/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Comma.Presheaf.Basic

/-!
# Presheaves over a representable presheaf

For an object `X` of a category `C`, presheaves of types on `C` lying over the representable
presheaf `yoneda.obj X` are the same as presheaves of types on the slice category `Over X`. This
specializes Mathlib's `overEquivPresheafCostructuredArrow`, which identifies presheaves over any
presheaf `A` with presheaves on `CostructuredArrow yoneda A`, using that `Over X` is equivalent to
`CostructuredArrow yoneda (yoneda.obj X)` because `yoneda` is fully faithful. Under this
equivalence the presheaf `yoneda.obj Y ⟶ yoneda.obj X` induced by an object `Y` of `Over X` goes
to the representable presheaf `yoneda.obj Y` on `Over X`.

## Main definitions

* `CategoryTheory.yonedaCompWhiskeringLeftIso`: for a fully faithful functor `F`, restricting
  `yoneda.obj (F.obj Y)` along `F` gives `yoneda.obj Y`.
* `CategoryTheory.overEquivCostructuredArrowYoneda X`: the equivalence between `Over X` and
  `CostructuredArrow yoneda (yoneda.obj X)`.
* `CategoryTheory.overYonedaEquivPresheafOver X`: the equivalence between `Over (yoneda.obj X)`
  and presheaves of types on `Over X`.
* `CategoryTheory.overYonedaEquivPresheafOverYonedaIso X`: the equivalence sends the object
  `yoneda.map Y.hom` of `Over (yoneda.obj X)` to `yoneda.obj Y`, naturally in `Y : Over X`.

## References

* M. Kashiwara, P. Schapira, *Categories and Sheaves*, Lemma 1.4.12
-/

public section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- For a fully faithful functor `F : C ⥤ D`, restricting the presheaf `yoneda.obj (F.obj Y)`
along `F` recovers `yoneda.obj Y`, naturally in `Y`. -/
noncomputable def yonedaCompWhiskeringLeftIso {D : Type*} [Category.{v} D] {F : C ⥤ D}
    (hF : F.FullyFaithful) : F ⋙ yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj F.op ≅ yoneda :=
  NatIso.ofComponents
    (fun Y ↦ NatIso.ofComponents (fun Z ↦ Equiv.toIso hF.homEquiv.symm)
      (fun f ↦ by ext; exact hF.map_injective (by simp)))
    (fun f ↦ by ext; exact hF.map_injective (by simp))

/-- The slice category `Over X` is equivalent to the category of costructured arrows from the
Yoneda embedding to `yoneda.obj X`, sending `f : Y ⟶ X` to `yoneda.map f`. -/
noncomputable def overEquivCostructuredArrowYoneda (X : C) :
    Over X ≌ CostructuredArrow yoneda (yoneda.obj X) :=
  (CostructuredArrow.post (𝟭 C) yoneda X).asEquivalence.trans
    (CostructuredArrow.mapNatIso yoneda.leftUnitor)

/-- Presheaves of types on `C` lying over the representable presheaf `yoneda.obj X` are equivalent
to presheaves of types on the slice category `Over X`. -/
noncomputable def overYonedaEquivPresheafOver (X : C) :
    Over (yoneda.obj X) ≌ ((Over X)ᵒᵖ ⥤ Type v) :=
  (overEquivPresheafCostructuredArrow (yoneda.obj X)).trans
    (overEquivCostructuredArrowYoneda X).op.symm.congrLeft

/-- The equivalence `overYonedaEquivPresheafOver X` sends the presheaf `yoneda.obj Y` lying over
`yoneda.obj X` through `yoneda.map Y.hom` to the representable presheaf `yoneda.obj Y` on
`Over X`, naturally in `Y : Over X`. -/
noncomputable def overYonedaEquivPresheafOverYonedaIso (X : C) :
    Over.post yoneda ⋙ (overYonedaEquivPresheafOver X).functor ≅ yoneda :=
  Functor.isoWhiskerLeft (overEquivCostructuredArrowYoneda X).functor
    (Functor.isoWhiskerRight
      (CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow (yoneda.obj X)) _) ≪≫
    yonedaCompWhiskeringLeftIso (overEquivCostructuredArrowYoneda X).fullyFaithfulFunctor

end CategoryTheory
