/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.NaturalTransformation.Cat
public import TauCeti.CategoryTheory.Sites.Descent.BandedMorphism.HomGroupoid
public import TauCeti.CategoryTheory.Sites.Descent.IsomTorsor.Action

/-!
# Restriction of fibre isomorphisms along arrows of the site

Let `b` be an `A`-banding of a pseudofunctor `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`, and `f : V ⟶ U` an
arrow of `C`. Pulling an isomorphism `p : x ≅ y` of the fibre over `U` back along `f` is a map of
`A(U)`-sets from `x ≅ y` to the isomorphisms `F(f) x ≅ F(f) y`, on which `A(U)` acts through the
restriction `A(U) → A(V)` (`AbelianBanding.restrictActionHom`), because pulling back carries the
band automorphism of `a` to the band automorphism of the restriction of `a`.

For a strong transformation `X : F ⟶ G`, the restriction comparison
`BandedMorphism.restrictionIso X f x : G(f) (X_U x) ≅ X_V (F(f) x)` is the inverse of the
naturality isomorphism of `X` along `f` at `x`. It is compatible with modifications
(`BandedMorphism.restrictionIso_modification`) and along the identity it is assembled from the
unit isomorphisms of `F` and `G` (`BandedMorphism.restrictionIso_id`). Pulling back an
isomorphism `p : y ≅ X_U x` and composing with it gives the restriction of fibre isomorphisms
`BandedMorphism.fiberIsomRestriction X f x y : (y ≅ X_U x) ⟶ (G(f) y ≅ X_V (F(f) x))`, again a
map of `A(U)`-sets for the restricted action (Olsson, Definitions 31.1 and Remarks 31.2, 31.5;
Groechenig, Wyss and Ziegler, Definition 2.6 and §2.2.1).

## Main declarations

* `CategoryTheory.Pseudofunctor.AbelianBanding.restrictActionHom`, with
  `restrictActionHom_hom_apply`, `restrictActionHom_hom_trans`, `restrictActionHom_hom_refl`.
* `CategoryTheory.Pseudofunctor.BandedMorphism.restrictionIso`, with `restrictionIso_hom`,
  `restrictionIso_inv`, `restrictionIso_modification` and `restrictionIso_id`.
* `CategoryTheory.Pseudofunctor.BandedMorphism.fiberIsomRestriction`, with
  `fiberIsomRestriction_hom_apply` and `fiberIsomRestriction_id`.

## References

* [Martin Olsson, *Stacks* (lecture notes, notes by A. Geraschenko et al.)](https://stacky.net/files/written/Stacks/Stacks.pdf),
  Definition 31.1, Remark 31.2, Lemma 31.3 and Remark 31.5
* [Michael Groechenig, Dimitri Wyss and Paul Ziegler, *Mirror symmetry for moduli of Higgs
  bundles via p-adic integration*](https://doi.org/10.1007/s00222-020-00957-8),
  Definition 2.6 and §2.2.1
-/

public section

universe w v u v' u'

open CategoryTheory Opposite Bicategory
open scoped Pseudofunctor.StrongTrans

namespace CategoryTheory.Pseudofunctor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A : Sheaf J AddCommGrpCat.{w}} {U V : C} (f : V ⟶ U)

namespace AbelianBanding

variable {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}} (b : F.AbelianBanding J A)

/-- **Restriction of fibre isomorphisms** along `f : V ⟶ U`: pulling back `p : x ≅ y` along `f`
is a map of `A(U)`-sets from `x ≅ y` to the isomorphisms `F(f) x ≅ F(f) y`, on which `A(U)` acts
through the restriction `A(U) → A(V)` (`AbelianBanding.mapIso_act`). It needs no isomorphism
`x ≅ y` to exist. -/
def restrictActionHom (x y : F.obj (.mk (op U))) :
    b.fiberAction x y ⟶
      (Action.res _ (AddMonoidHom.toMultiplicative (A.obj.map f.op).hom)).obj
        (b.fiberAction ((F.map f.op.toLoc).toFunctor.obj x)
          ((F.map f.op.toLoc).toFunctor.obj y)) where
  hom := TypeCat.ofHom fun p : x ≅ y ↦ (F.map f.op.toLoc).toFunctor.mapIso p
  comm a := by
    ext (p : x ≅ y)
    -- The carriers of `fiberAction` are isomorphisms only after unfolding; see
    -- `AbelianBanding.postcomposeActionIso`.
    change (F.map f.op.toLoc).toFunctor.mapIso (b.act p a) =
      b.act ((F.map f.op.toLoc).toFunctor.mapIso p) (.ofAdd (A.obj.map f.op a.toAdd))
    exact b.mapIso_act f p a

/-- `restrictActionHom` pulls back `p` along `f`. -/
@[simp]
theorem restrictActionHom_hom_apply {x y : F.obj (.mk (op U))} (p : x ≅ y) :
    (b.restrictActionHom f x y).hom p = (F.map f.op.toLoc).toFunctor.mapIso p :=
  (rfl)

/-- Restriction of a composite is the composite of the restrictions. -/
theorem restrictActionHom_hom_trans {x y z : F.obj (.mk (op U))} (p : x ≅ y) (q : y ≅ z) :
    (b.restrictActionHom f x z).hom (p ≪≫ q) =
      (b.restrictActionHom f x y).hom p ≪≫ (b.restrictActionHom f y z).hom q :=
  Functor.mapIso_trans _ p q

/-- Restriction of an identity isomorphism is the identity. -/
theorem restrictActionHom_hom_refl (x : F.obj (.mk (op U))) :
    (b.restrictActionHom f x x).hom (Iso.refl x) = Iso.refl _ :=
  Functor.mapIso_refl _ x

end AbelianBanding

namespace BandedMorphism

variable {F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}

/-- **The restriction comparison** of a strong transformation `X : F ⟶ G` along `f : V ⟶ U` at
`x`: the isomorphism `G(f) (X_U x) ≅ X_V (F(f) x)`, the inverse of the naturality isomorphism of
`X` along `f` at `x`. -/
noncomputable def restrictionIso (X : F ⟶ G) (x : F.obj (.mk (op U))) :
    (G.map f.op.toLoc).toFunctor.obj ((X.app (.mk (op U))).toFunctor.obj x) ≅
      (X.app (.mk (op V))).toFunctor.obj ((F.map f.op.toLoc).toFunctor.obj x) :=
  (X.naturalityObjIso f.op.toLoc x).symm

@[simp]
theorem restrictionIso_hom (X : F ⟶ G) (x : F.obj (.mk (op U))) :
    (restrictionIso f X x).hom = (X.naturality f.op.toLoc).inv.toNatTrans.app x := by
  rw [restrictionIso, Iso.symm_hom, StrongTrans.naturalityObjIso_inv]

@[simp]
theorem restrictionIso_inv (X : F ⟶ G) (x : F.obj (.mk (op U))) :
    (restrictionIso f X x).inv = (X.naturality f.op.toLoc).hom.toNatTrans.app x := by
  rw [restrictionIso, Iso.symm_inv, StrongTrans.naturalityObjIso_hom]

/-- **The restriction comparison along the identity** is the unit isomorphism of `G` at `X_U x`
followed by the image under `X_U` of the inverse unit isomorphism of `F` at `x`. -/
theorem restrictionIso_id (X : F ⟶ G) (x : F.obj (.mk (op U))) :
    (restrictionIso (𝟙 U) X x).hom =
      (G.mapId (.mk (op U))).hom.toNatTrans.app ((X.app (.mk (op U))).toFunctor.obj x) ≫
        (X.app (.mk (op U))).toFunctor.map ((F.mapId (.mk (op U))).inv.toNatTrans.app x) := by
  rw [restrictionIso_hom]
  exact (StrongTrans.naturality_id_inv_app X (.mk (op U)) x).trans (by simp)

variable {bF : F.AbelianBanding J A} {bG : G.AbelianBanding J A}

/-- **Modifications commute with the restriction comparisons**: for `m : X ⟶ Y`, pulling back the
component of `m` at `x` along `f` and comparing with `Y` is comparing with `X` and then taking the
component of `m` at `F(f) x`. -/
theorem restrictionIso_modification [∀ U : C, IsGroupoid (G.obj (.mk (op U)))]
    {X Y : HomCategory bF bG} (m : X ⟶ Y)
    (x : F.obj (.mk (op U))) :
    (G.map f.op.toLoc).toFunctor.mapIso (componentIso m U x) ≪≫ restrictionIso f Y.obj x =
      restrictionIso f X.obj x ≪≫ componentIso m V ((F.map f.op.toLoc).toFunctor.obj x) := by
  ext
  -- Evaluate the naturality of `m` along `f` at `x` and move the comparisons across.
  have h := congrArg (fun φ ↦ φ.toNatTrans.app x) (m.hom.as.naturality f.op.toLoc)
  rw [Cat.Hom₂.comp_app, Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app] at h
  rw [Iso.trans_hom, Iso.trans_hom, restrictionIso, restrictionIso, Iso.symm_hom, Iso.symm_hom,
    Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq, StrongTrans.naturalityObjIso_hom,
    StrongTrans.naturalityObjIso_hom, Functor.mapIso_hom, componentIso_hom, componentIso_hom]
  exact h.symm

/-- **Restriction of fibre isomorphisms** for a band-preserving `X : F ⟶ G` along `f : V ⟶ U`:
the map of `A(U)`-sets from `y ≅ X_U x` to `G(f) y ≅ X_V (F(f) x)`, with `A(U)` acting on the
target through the restriction `A(U) → A(V)`, that pulls back `p` along `f` and composes with the
restriction comparison `restrictionIso f X x`. -/
noncomputable def fiberIsomRestriction (X : HomCategory bF bG) (x : F.obj (.mk (op U)))
    (y : G.obj (.mk (op U))) :
    bG.fiberAction y ((X.obj.app (.mk (op U))).toFunctor.obj x) ⟶
      (Action.res _ (AddMonoidHom.toMultiplicative (A.obj.map f.op).hom)).obj
        (bG.fiberAction ((G.map f.op.toLoc).toFunctor.obj y)
          ((X.obj.app (.mk (op V))).toFunctor.obj ((F.map f.op.toLoc).toFunctor.obj x))) :=
  bG.restrictActionHom f y _ ≫
    (Action.res _ (AddMonoidHom.toMultiplicative (A.obj.map f.op).hom)).map
      (bG.postcomposeActionIso (restrictionIso f X.obj x)).hom

/-- `fiberIsomRestriction` sends `p` to its pullback along `f` followed by the restriction
comparison. -/
@[simp]
theorem fiberIsomRestriction_hom_apply (X : HomCategory bF bG) (x : F.obj (.mk (op U)))
    {y : G.obj (.mk (op U))} (p : y ≅ (X.obj.app (.mk (op U))).toFunctor.obj x) :
    (fiberIsomRestriction f X x y).hom p =
      (G.map f.op.toLoc).toFunctor.mapIso p ≪≫ restrictionIso f X.obj x :=
  bG.postcomposeActionIso_hom_hom _ _

/-- **Restriction of fibre isomorphisms along the identity**: `p` goes to the unit isomorphism of
`G` at `y`, then `p`, then the image under `X_U` of the inverse unit isomorphism of `F` at `x`. -/
theorem fiberIsomRestriction_id (X : HomCategory bF bG) (x : F.obj (.mk (op U)))
    {y : G.obj (.mk (op U))} (p : y ≅ (X.obj.app (.mk (op U))).toFunctor.obj x) :
    ((fiberIsomRestriction (𝟙 U) X x y).hom p).hom =
      (G.mapId (.mk (op U))).hom.toNatTrans.app y ≫ p.hom ≫
        (X.obj.app (.mk (op U))).toFunctor.map ((F.mapId (.mk (op U))).inv.toNatTrans.app x) := by
  rw [fiberIsomRestriction_hom_apply, Iso.trans_hom, restrictionIso_id, Functor.mapIso_hom]
  -- Move the unit isomorphism of `G` past `p` by its naturality.
  exact (G.mapId (.mk (op U))).hom.toNatTrans.naturality_assoc p.hom _

end BandedMorphism

end CategoryTheory.Pseudofunctor
