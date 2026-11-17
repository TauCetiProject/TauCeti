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
  `Sheaf.composeAndSheafify J F` at `Φ` is `F` applied to the fibre. On germs it sends the germ
  of the sheafification of a section of `G ⋙ F` to `F` applied to the germ of the section
  (`toSheafify_toPresheafFiber_composeAndSheafifyCompSheafFiberIso_hom_app`).
* `presheafFiber_map_toSheafify_presheafToSheafCompSheafFiberIso_hom_app`: Mathlib's comparison
  `presheafToSheafCompSheafFiberIso` inverts the fibre of the sheafification map.
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

omit [LocallySmall.{w} C] in
/-- The comparison `presheafToSheafCompSheafFiberIso` between the fibre of the sheafification of a
presheaf `P` and the fibre of `P` is inverse to the fibre of the sheafification map of `P`. -/
@[reassoc]
lemma presheafFiber_map_toSheafify_presheafToSheafCompSheafFiberIso_hom_app (P : Cᵒᵖ ⥤ B) :
    Φ.presheafFiber.map (CategoryTheory.toSheafify J P) ≫
        (Φ.presheafToSheafCompSheafFiberIso B).hom.app P = 𝟙 _ := by
  -- Mathlib defines the comparison as the inverse of the components
  -- `asIso (Φ.presheafFiber.map (toSheafify J P))`.
  simp only [presheafToSheafCompSheafFiberIso]
  exact IsIso.hom_inv_id _

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
  -- The component at `G` of the composite isomorphism is, by definition, the composite of the
  -- components of the two whiskered isomorphisms.
  exact ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ (Φ.presheafFiberCompIso F).hom.app G.obj)
      (Φ.presheafFiber_map_toSheafify_presheafToSheafCompSheafFiberIso_hom_app (G.obj ⋙ F)))).trans
    (Category.id_comp _)

/-- On germs, `composeAndSheafifyCompSheafFiberIso` sends the germ at `x` of the sheafification of a
section of `G ⋙ F` over `X` to `F` applied to the germ of that section of `G`. -/
@[reassoc]
lemma toSheafify_toPresheafFiber_composeAndSheafifyCompSheafFiberIso_hom_app (G : Sheaf J A)
    (X : C) (x : Φ.fiber.obj X) :
    (CategoryTheory.toSheafify J (G.obj ⋙ F)).app (Opposite.op X) ≫
        Φ.toPresheafFiber X x ((Sheaf.composeAndSheafify J F).obj G).obj ≫
          (Φ.composeAndSheafifyCompSheafFiberIso F).hom.app G =
      F.map (Φ.toPresheafFiber X x G.obj) := by
  refine (Φ.toPresheafFiber_naturality_assoc (CategoryTheory.toSheafify J (G.obj ⋙ F)) X x
    ((Φ.composeAndSheafifyCompSheafFiberIso F).hom.app G)).symm.trans ?_
  rw [presheafFiber_map_toSheafify_composeAndSheafifyCompSheafFiberIso_hom_app]
  exact Φ.toPresheafFiber_presheafFiberCompIso_hom_app F X x G.obj

/-- On germs, the inverse of `composeAndSheafifyCompSheafFiberIso` sends `F` applied to the germ at
`x` of a section of `G` over `X` to the germ of the sheafification of that section of `G ⋙ F`. -/
@[reassoc]
lemma map_toPresheafFiber_composeAndSheafifyCompSheafFiberIso_inv_app (G : Sheaf J A) (X : C)
    (x : Φ.fiber.obj X) :
    F.map (Φ.toPresheafFiber X x G.obj) ≫ (Φ.composeAndSheafifyCompSheafFiberIso F).inv.app G =
      (CategoryTheory.toSheafify J (G.obj ⋙ F)).app (Opposite.op X) ≫
        Φ.toPresheafFiber X x ((Sheaf.composeAndSheafify J F).obj G).obj := by
  exact ((Φ.composeAndSheafifyCompSheafFiberIso F).app G).comp_inv_eq.mpr
    ((Φ.toSheafify_toPresheafFiber_composeAndSheafifyCompSheafFiberIso_hom_app F G X x).symm.trans
      (Category.assoc _ _ _).symm)

end CategoryTheory.GrothendieckTopology.Point
