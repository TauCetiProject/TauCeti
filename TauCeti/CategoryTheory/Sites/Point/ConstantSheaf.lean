/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# Fibres of constant sheaves at a point of a site

Let `Φ` be a point of a site `(C, J)`. The fibre at `Φ` of the constant presheaf with value `M`
is `M`, naturally in `M`, since the category of elements of the fibre functor of `Φ` is
cofiltered, hence connected. Composing with Mathlib's identification
`CategoryTheory.GrothendieckTopology.Point.presheafToSheafCompSheafFiberIso` of the fibre of a
sheafification with the fibre of the presheaf, the fibre at `Φ` of the constant sheaf with value
`M` is `M`, naturally in `M`.

## Main declarations

* `CategoryTheory.GrothendieckTopology.Point.presheafFiberConstNatIso`: the fibre of the constant
  presheaf with value `M` is `M`, naturally.
* `CategoryTheory.GrothendieckTopology.Point.sheafFiberConstantSheafNatIso`: the fibre of the
  constant sheaf with value `M` is `M`, naturally.
* `CategoryTheory.GrothendieckTopology.Point.presheafFiberConstIso_inv`,
  `CategoryTheory.GrothendieckTopology.Point.sheafFiberConstantSheafIso_inv`: the inverse
  identifications are germs of constant sections.
-/

public section

universe w v u u' v'

open CategoryTheory Limits Opposite

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (Φ : Point.{w} J) {A : Type u'} [Category.{v'} A] [HasColimitsOfSize.{w, w} A]

/-- The fibre of the constant presheaf with value `M` is `M`, because the category of elements of
the fibre functor of a point is cofiltered, hence connected. -/
noncomputable def presheafFiberConstIso (M : A) :
    Φ.presheafFiber.obj ((Functor.const Cᵒᵖ).obj M) ≅ M :=
  (colimit.isColimit _).coconePointUniqueUpToIso (isColimitConstCocone _ M)

/-- Under `presheafFiberConstIso`, every germ of the constant presheaf is the identity of `M`. -/
@[reassoc (attr := simp)]
lemma toPresheafFiber_presheafFiberConstIso_hom (M : A) (X : C) (x : Φ.fiber.obj X) :
    Φ.toPresheafFiber X x ((Functor.const Cᵒᵖ).obj M) ≫ (Φ.presheafFiberConstIso M).hom =
      𝟙 M :=
  (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom _ _

/-- The inverse of `presheafFiberConstIso` is the germ of the constant presheaf at any element
`x` of the fibre of `Φ`. -/
lemma presheafFiberConstIso_inv (M : A) (X : C) (x : Φ.fiber.obj X) :
    (Φ.presheafFiberConstIso M).inv = Φ.toPresheafFiber X x ((Functor.const Cᵒᵖ).obj M) :=
  ((Iso.comp_hom_eq_id _).1 (Φ.toPresheafFiber_presheafFiberConstIso_hom M X x)).symm

variable (A) in
/-- The fibre of the constant presheaf with value `M` is `M`, naturally in `M`. -/
noncomputable def presheafFiberConstNatIso : Functor.const Cᵒᵖ ⋙ Φ.presheafFiber ≅ 𝟭 A :=
  NatIso.ofComponents Φ.presheafFiberConstIso fun f ↦
    Φ.presheafFiber_hom_ext fun X x ↦ by simp [toPresheafFiber_naturality_assoc]

@[simp]
lemma presheafFiberConstNatIso_app (M : A) :
    (Φ.presheafFiberConstNatIso A).app M = Φ.presheafFiberConstIso M :=
  (rfl)

variable [HasWeakSheafify J A] [HasProducts.{w} A]

/-- **The fibre of a constant sheaf.** The fibre at any point of the constant sheaf with value
`M` is `M`. -/
noncomputable def sheafFiberConstantSheafIso (M : A) :
    Φ.sheafFiber.obj ((constantSheaf J A).obj M) ≅ M :=
  (Φ.presheafToSheafCompSheafFiberIso A).app _ ≪≫ Φ.presheafFiberConstIso M

/-- Under `sheafFiberConstantSheafIso`, the germ of the image in the constant sheaf of the
constant section with value `M` is the identity of `M`. -/
@[reassoc (attr := simp)]
lemma toSheafify_toPresheafFiber_sheafFiberConstantSheafIso_hom (M : A) (X : C)
    (x : Φ.fiber.obj X) :
    (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op X) ≫
      Φ.toPresheafFiber X x ((constantSheaf J A).obj M).obj ≫
        (Φ.sheafFiberConstantSheafIso M).hom = 𝟙 M := by
  -- `(constantSheaf J A).obj M` is not reducibly `sheafify J _`, which blocks `rw` and `simp`;
  -- by definition, `(Φ.sheafFiberConstantSheafIso M).hom` is the inverse of the fibre of
  -- `toSheafify J _` followed by `(Φ.presheafFiberConstIso M).hom`.
  let t := CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M)
  exact (Φ.toPresheafFiber_naturality_assoc t X x _).symm.trans <|
    (congrArg (Φ.toPresheafFiber X x _ ≫ ·)
      (IsIso.hom_inv_id_assoc (Φ.presheafFiber.map t) (Φ.presheafFiberConstIso M).hom)).trans
      (Φ.toPresheafFiber_presheafFiberConstIso_hom M X x)

/-- The inverse of `sheafFiberConstantSheafIso` is the germ at any element `x` of the fibre of
`Φ` of the image in the constant sheaf of the constant section with value `M`. -/
lemma sheafFiberConstantSheafIso_inv (M : A) (X : C) (x : Φ.fiber.obj X) :
    (Φ.sheafFiberConstantSheafIso M).inv =
      (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op X) ≫
        Φ.toPresheafFiber X x ((constantSheaf J A).obj M).obj :=
  ((Iso.comp_hom_eq_id _).1 ((Category.assoc _ _ _).trans
    (Φ.toSheafify_toPresheafFiber_sheafFiberConstantSheafIso_hom M X x))).symm

variable (A) in
/-- **The fibre of a constant sheaf, naturally.** The fibre at any point of the constant sheaf
with value `M` is `M`, naturally in `M`. -/
noncomputable def sheafFiberConstantSheafNatIso : constantSheaf J A ⋙ Φ.sheafFiber ≅ 𝟭 A :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Functor.const Cᵒᵖ) (Φ.presheafToSheafCompSheafFiberIso A) ≪≫
      Φ.presheafFiberConstNatIso A

@[simp]
lemma sheafFiberConstantSheafNatIso_app (M : A) :
    (Φ.sheafFiberConstantSheafNatIso A).app M = Φ.sheafFiberConstantSheafIso M :=
  Iso.ext (Category.id_comp _)

end CategoryTheory.GrothendieckTopology.Point
