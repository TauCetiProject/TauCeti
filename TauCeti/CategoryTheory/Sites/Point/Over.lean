/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Point.Over
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# Fibres at a point of restrictions and of constant sheaves

Let `Φ` be a point of a site `(C, J)`, let `X : C` and let `x : Φ.fiber.obj X`. Mathlib's
`CategoryTheory.GrothendieckTopology.Point.over` is the induced point `Φ.over x` of the site
`(Over X, J.over X)`. This file shows that restricting a presheaf or a sheaf to `Over X` does not
change its fibre: the fibre at `Φ.over x` of the restriction `F.over X` is the fibre of `F` at
`Φ` (`CategoryTheory.GrothendieckTopology.Point.sheafFiberOverIso`). The reason is that the
category of elements of the fibre functor of `Φ.over x` is the slice of the category of elements
of `Φ.fiber` over `(X, x)`, and the projection from a slice of a cofiltered category is initial.

It also computes the fibre of a constant sheaf: the fibre at any point of the constant sheaf with
value `M` is `M` (`CategoryTheory.GrothendieckTopology.Point.sheafFiberConstantSheafIso`), since
the category of elements of a fibre functor is cofiltered, hence connected.

## Main declarations

* `CategoryTheory.GrothendieckTopology.Point.presheafFiberOverNatIso`,
  `CategoryTheory.GrothendieckTopology.Point.sheafFiberOverNatIso`: the fibre at `Φ.over x` of
  the restriction to `Over X` is the fibre at `Φ`, naturally.
* `CategoryTheory.GrothendieckTopology.Point.presheafFiberConstIso`,
  `CategoryTheory.GrothendieckTopology.Point.sheafFiberConstantSheafIso`: the fibre of a constant
  presheaf or of a constant sheaf with value `M` is `M`.

## References

* A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé IV, §6.8, for points of a localized topos.
-/

@[expose] public section

universe w v u u' v'

open CategoryTheory Limits Opposite

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (Φ : Point.{w} J) {A : Type u'} [Category.{v'} A]

section Over

variable [LocallySmall.{w} C] {X : C} (x : Φ.fiber.obj X)

/-- The functor from the category of elements of the fibre functor of `Φ.over x` to the category
of elements of `Φ.fiber`, sending a point `y` of `Y : Over X` lying over `x` to the point `y` of
`Y.left`. It identifies the source with the slice over `(X, x)`. -/
@[simps]
def overElementsForget : (Φ.over x).fiber.Elements ⥤ Φ.fiber.Elements where
  obj u := Φ.fiber.elementsMk u.obj.left u.val.1
  map f := Functor.Elements.homMk f.hom.left (congrArg Subtype.val f.map_val)

/-- The projection from the slice of the cofiltered category `Φ.fiber.Elements` over `(X, x)` is
initial. -/
instance initial_overElementsForget : (Φ.overElementsForget x).Initial :=
  Functor.initial_of_exists_of_isCofiltered _
    (fun d ↦
      let b := IsCofiltered.minToRight d (Φ.fiber.elementsMk X x)
      ⟨(Φ.over x).fiber.elementsMk (Over.mk b.hom)
          ⟨_, (FunctorToTypes.mem_fromOverSubfunctor_iff _ _ _).2 b.map_val⟩,
        ⟨IsCofiltered.minToLeft d (Φ.fiber.elementsMk X x)⟩⟩)
    (fun {_ c} s s' ↦
      let t := IsCofiltered.eqHom s s'
      have hc : Φ.fiber.map c.obj.hom c.val.1 = x :=
        (FunctorToTypes.mem_fromOverSubfunctor_iff _ _ _).1 c.val.2
      ⟨(Φ.over x).fiber.elementsMk (Over.mk (t.hom ≫ c.obj.hom))
          ⟨(IsCofiltered.eq s s').val, (FunctorToTypes.mem_fromOverSubfunctor_iff _ _ _).2
            ((Functor.map_comp_apply Φ.fiber t.hom c.obj.hom _).trans
              ((congrArg (Φ.fiber.map c.obj.hom) t.map_val).trans hc))⟩,
        Functor.Elements.homMk (Over.homMk t.hom) (Subtype.ext t.map_val),
        Functor.Elements.hom_ext (congrArg Functor.Elements.Hom.hom
          (IsCofiltered.eq_condition s s'))⟩)

variable [HasColimitsOfSize.{w, w} A]

/-- The fibre at the point `Φ.over x` of the restriction of a presheaf `P` to `Over X` is the
fibre of `P` at `Φ`. -/
noncomputable def presheafFiberOverIso (P : Cᵒᵖ ⥤ A) :
    (Φ.over x).presheafFiber.obj ((Over.forget X).op ⋙ P) ≅ Φ.presheafFiber.obj P :=
  Functor.Final.colimitIso (Φ.overElementsForget x).op ((Functor.Elements.π Φ.fiber).op ⋙ P)

/-- Under `presheafFiberOverIso`, the germ at `Φ.over x` of a section over `Y : Over X` is its
germ at `Φ`. -/
@[reassoc (attr := simp)]
lemma toPresheafFiber_presheafFiberOverIso_hom (P : Cᵒᵖ ⥤ A) (Y : Over X)
    (y : (Φ.over x).fiber.obj Y) :
    (Φ.over x).toPresheafFiber Y y ((Over.forget X).op ⋙ P) ≫
      (Φ.presheafFiberOverIso x P).hom = Φ.toPresheafFiber Y.left y.1 P :=
  Functor.Final.ι_colimitIso_hom (Φ.overElementsForget x).op
    ((Functor.Elements.π Φ.fiber).op ⋙ P) (op ((Φ.over x).fiber.elementsMk Y y))

/-- Under the inverse of `presheafFiberOverIso`, the germ at `Φ` of a section over `Y.left`,
through a point `y` over `x`, is its germ at `Φ.over x`. -/
@[reassoc (attr := simp)]
lemma toPresheafFiber_presheafFiberOverIso_inv (P : Cᵒᵖ ⥤ A) (Y : Over X)
    (y : (Φ.over x).fiber.obj Y) :
    Φ.toPresheafFiber Y.left y.1 P ≫ (Φ.presheafFiberOverIso x P).inv =
      (Φ.over x).toPresheafFiber Y y ((Over.forget X).op ⋙ P) := by
  rw [Iso.comp_inv_eq, toPresheafFiber_presheafFiberOverIso_hom]

variable (A) in
/-- Restricting presheaves to `Over X` and taking the fibre at `Φ.over x` is the fibre functor of
`Φ`. -/
@[simps!]
noncomputable def presheafFiberOverNatIso :
    (Functor.whiskeringLeft _ _ A).obj (Over.forget X).op ⋙ (Φ.over x).presheafFiber ≅
      Φ.presheafFiber :=
  NatIso.ofComponents (Φ.presheafFiberOverIso x) fun {P Q} f ↦
    (Φ.over x).presheafFiber_hom_ext fun Y y ↦ by simp [toPresheafFiber_naturality_assoc]

variable (A) in
/-- **The fibre of a restriction.** Restricting sheaves to `Over X` and taking the fibre at
`Φ.over x` is the fibre functor of `Φ`. -/
@[simps!]
noncomputable def sheafFiberOverNatIso :
    J.overPullback A X ⋙ (Φ.over x).sheafFiber ≅ Φ.sheafFiber :=
  Functor.isoWhiskerLeft (sheafToPresheaf J A) (Φ.presheafFiberOverNatIso A x)

/-- The fibre at `Φ.over x` of the restriction `F.over X` of a sheaf is the fibre of `F` at
`Φ`. -/
noncomputable abbrev sheafFiberOverIso (F : Sheaf J A) :
    (Φ.over x).sheafFiber.obj (F.over X) ≅ Φ.sheafFiber.obj F :=
  (Φ.sheafFiberOverNatIso A x).app F

end Over

section Constant

variable [HasColimitsOfSize.{w, w} A]

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

variable [HasWeakSheafify J A] [HasProducts.{w} A]

/-- **The fibre of a constant sheaf.** The fibre at any point of the constant sheaf with value
`M` is `M`. -/
noncomputable def sheafFiberConstantSheafIso (M : A) :
    Φ.sheafFiber.obj ((constantSheaf J A).obj M) ≅ M :=
  (Φ.presheafToSheafCompSheafFiberIso A).app _ ≪≫ Φ.presheafFiberConstIso M

end Constant

end CategoryTheory.GrothendieckTopology.Point
