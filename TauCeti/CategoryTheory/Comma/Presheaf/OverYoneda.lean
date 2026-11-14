/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Comma.Presheaf.Basic
public import TauCeti.CategoryTheory.Comma.Over.CostructuredArrow

/-!
# Presheaves over a representable presheaf

For an object `X` of a category `C`, presheaves of types on `C` lying over the representable
presheaf `yoneda.obj X` are the same as presheaves of types on the slice category `Over X`. This
specializes Mathlib's `overEquivPresheafCostructuredArrow`, which identifies presheaves over any
presheaf `A` with presheaves on `CostructuredArrow yoneda A`, using that `Over X` is equivalent to
`CostructuredArrow F (F.obj X)` for any fully faithful functor `F`, in particular for `yoneda`
(`CategoryTheory.Functor.FullyFaithful.overEquivCostructuredArrow`).
Under this equivalence the presheaf `yoneda.obj Y ⟶ yoneda.obj X` induced by an object `Y` of
`Over X` goes to the representable presheaf `yoneda.obj Y` on `Over X`.

## Main definitions

* `TauCeti.overYonedaEquivPresheafOver X`: the equivalence between `Over (yoneda.obj X)`
  and presheaves of types on `Over X`.
* `TauCeti.overYonedaEquivPresheafOverYonedaIso X`: the equivalence sends the object
  `yoneda.map Y.hom` of `Over (yoneda.obj X)` to `yoneda.obj Y`, naturally in `Y : Over X`.

## References

* M. Kashiwara, P. Schapira, *Categories and Sheaves*, Lemma 1.4.12
-/

public section

universe v u

namespace TauCeti

open CategoryTheory Opposite OverPresheafAux

variable {C : Type u} [Category.{v} C]

/-- Presheaves of types on `C` lying over the representable presheaf `yoneda.obj X` are equivalent
to presheaves of types on the slice category `Over X`. -/
@[expose]
noncomputable def overYonedaEquivPresheafOver (X : C) :
    Over (yoneda.obj X) ≌ ((Over X)ᵒᵖ ⥤ Type v) :=
  (overEquivPresheafCostructuredArrow (yoneda.obj X)).trans
    (Yoneda.fullyFaithful.overEquivCostructuredArrow X).op.symm.congrLeft

/-- The value at `Y : Over X` of the presheaf attached to `p : F ⟶ yoneda.obj X` consists of the
sections of `F` over `Y.left` that `p` sends to `Y.hom`. -/
@[simp]
lemma overYonedaEquivPresheafOver_functor_obj_obj (X : C) (F : Over (yoneda.obj X)) (Y : Over X) :
    ((overYonedaEquivPresheafOver X).functor.obj F).obj (op Y) =
      OverArrows F.hom (yoneda.map Y.hom) := rfl

@[simp]
lemma overYonedaEquivPresheafOver_functor_obj_map (X : C) (F : Over (yoneda.obj X)) {Y Z : Over X}
    (f : Y ⟶ Z) :
    ((overYonedaEquivPresheafOver X).functor.obj F).map f.op =
      TypeCat.ofHom fun u ↦ u.map₂ f.left (by simp [← Functor.map_comp]) := rfl

@[simp]
lemma overYonedaEquivPresheafOver_functor_map_app (X : C) {F G : Over (yoneda.obj X)}
    (ε : F ⟶ G) (Y : Over X) :
    ((overYonedaEquivPresheafOver X).functor.map ε).app (op Y) =
      TypeCat.ofHom fun u ↦ u.map₁ ε.left (Over.w ε) := rfl

/-- The inverse of `overYonedaEquivPresheafOver X` restricts a presheaf on `Over X` to
`CostructuredArrow yoneda (yoneda.obj X)` and applies the inverse of Mathlib's
`overEquivPresheafCostructuredArrow`. -/
lemma overYonedaEquivPresheafOver_inverse_obj (X : C) (P : (Over X)ᵒᵖ ⥤ Type v) :
    (overYonedaEquivPresheafOver X).inverse.obj P =
      (overEquivPresheafCostructuredArrow (yoneda.obj X)).inverse.obj
        ((Yoneda.fullyFaithful.overEquivCostructuredArrow X).inverse.op ⋙ P) := rfl

/-- The equivalence `overYonedaEquivPresheafOver X` sends the presheaf `yoneda.obj Y` lying over
`yoneda.obj X` through `yoneda.map Y.hom` to the representable presheaf `yoneda.obj Y` on
`Over X`, naturally in `Y : Over X`. -/
noncomputable def overYonedaEquivPresheafOverYonedaIso (X : C) :
    Over.post yoneda ⋙ (overYonedaEquivPresheafOver X).functor ≅ yoneda :=
  Functor.isoWhiskerLeft (Yoneda.fullyFaithful.overEquivCostructuredArrow X).functor
    (Functor.isoWhiskerRight
      (CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow (yoneda.obj X)) _) ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight uliftYonedaIsoYoneda.{v}.symm _) ≪≫
    Functor.FullyFaithful.compUliftYonedaCompWhiskeringLeft
      (Yoneda.fullyFaithful.overEquivCostructuredArrow X).fullyFaithfulFunctor ≪≫
    uliftYonedaIsoYoneda

lemma overYonedaEquivPresheafOverYonedaIso_inv_app_app_val (X : C) (Y Z : Over X) (f : Z ⟶ Y) :
    (((overYonedaEquivPresheafOverYonedaIso X).inv.app Y).app (op Z) f).val = f.left := (rfl)

lemma overYonedaEquivPresheafOverYonedaIso_hom_app_app_left (X : C) (Y Z : Over X)
    (u : ((Over.post yoneda ⋙ (overYonedaEquivPresheafOver X).functor).obj Y).obj (op Z)) :
    (((overYonedaEquivPresheafOverYonedaIso X).hom.app Y).app (op Z) u).left = u.val := by
  rw [← overYonedaEquivPresheafOverYonedaIso_inv_app_app_val, ← ConcreteCategory.comp_apply,
    ← NatTrans.comp_app, Iso.hom_inv_id_app]
  rfl

end TauCeti
