/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.CategoryTheory.Sites.PreservesSheafification

/-!
# Fibres of sheafified compositions at a point of a site

Let `Φ` be a point of a site `(C, J)` and `F : A ⥤ B` a functor preserving filtered colimits.
For a sheaf `G` with values in `A`, the composition `G ⋙ F` need not be a sheaf, and
`CategoryTheory.Sheaf.composeAndSheafify J F` sends `G` to the sheafification of `G ⋙ F`. Its
fibre at `Φ` is `F` applied to the fibre of `G`: sheafification does not change fibres
(`CategoryTheory.GrothendieckTopology.Point.presheafToSheafCompSheafFiberIso`), and fibres of
presheaves commute with `F` (`CategoryTheory.GrothendieckTopology.Point.presheafFiberCompIso`).

For sheaves of modules and `F` the extension of scalars along a ring homomorphism, this says that
extension of scalars of sheaves commutes with stalks. Restriction of scalars preserves sheaves,
and its compatibility with fibres is Mathlib's
`CategoryTheory.GrothendieckTopology.Point.sheafFiberCompIso`.

## Main declarations

* `CategoryTheory.GrothendieckTopology.Point.composeAndSheafifyCompSheafFiberIso`: the fibre of
  `Sheaf.composeAndSheafify J F` at `Φ` is `F` applied to the fibre.
-/

public section

universe w v u u' v' u'' v''

open CategoryTheory Limits

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (Φ : Point.{w} J)
  {A : Type u'} [Category.{v'} A] [HasColimitsOfSize.{w, w} A]
  {B : Type u''} [Category.{v''} B] [HasColimitsOfSize.{w, w} B] [HasProducts.{w} B]
  [HasWeakSheafify J B]
  (F : A ⥤ B) [LocallySmall.{w} C] [PreservesFilteredColimitsOfSize.{w, w} F]

/-- The fibre at a point of the sheafification of the composition of a sheaf with a functor `F`
preserving filtered colimits is `F` applied to the fibre of the sheaf. -/
noncomputable def composeAndSheafifyCompSheafFiberIso :
    Sheaf.composeAndSheafify J F ⋙ Φ.sheafFiber ≅ Φ.sheafFiber ⋙ F :=
  Functor.isoWhiskerLeft (sheafToPresheaf J A ⋙ (Functor.whiskeringRight _ _ _).obj F)
      (Φ.presheafToSheafCompSheafFiberIso B) ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf J A) (Φ.presheafFiberCompIso F)

/-- Under `composeAndSheafifyCompSheafFiberIso`, the fibre of the sheafification map of `G ⋙ F`
followed by the comparison is the comparison `presheafFiberCompIso` for the presheaf `G`. -/
@[reassoc]
lemma presheafFiber_map_toSheafify_composeAndSheafifyCompSheafFiberIso_hom_app (G : Sheaf J A) :
    Φ.presheafFiber.map (CategoryTheory.toSheafify J (G.obj ⋙ F)) ≫
        (Φ.composeAndSheafifyCompSheafFiberIso F).hom.app G =
      (Φ.presheafFiberCompIso F).hom.app G.obj := by
  simp only [composeAndSheafifyCompSheafFiberIso, presheafToSheafCompSheafFiberIso]
  exact IsIso.hom_inv_id_assoc _ _

end CategoryTheory.GrothendieckTopology.Point
