/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Descent.BandedMorphism.HomGroupoid
public import TauCeti.CategoryTheory.Sites.Descent.IsomTorsor.Action

/-!
# Fibre actions of band-preserving transformations

Let `F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` carry `A`-bandings `bF`, `bG`, with groupoid fibres of
`G`. For an object `U` of `C`, objects `x` of the fibre of `F` and `y` of the fibre of `G` over
`U`, sending a band-preserving transformation `X : F ⟶ G` to the `A(U)`-set of isomorphisms
`y ≅ X_U x` is a functor `BandedMorphism.fiberIsomActionFunctor` from the groupoid
`BandedMorphism.HomCategory bF bG` to `A(U)`-sets: an arrow `m : X ⟶ Y` acts by postcomposition
with its component `X_U x ≅ Y_U x`.

In the self case `F = G`, `bF = bG = b`, an isomorphism `e : x ≅ x'` of the fibre over `U`
transports the `A(U)`-set `x ≅ X_U x` to `x' ≅ X_U x'` by `p ↦ e⁻¹ ≫ p ≫ X_U e`
(`BandedMorphism.selfTransportActionIso`), naturally in `X`
(`BandedMorphism.selfTransportNatIso`). Because `X` preserves the band, the transport does not
depend on `e` (`BandedMorphism.selfTransportActionIso_independent`): any two isomorphisms
`x ≅ x'` differ by a band automorphism of `x`, which `X_U` carries to the band automorphism of
`X_U x`, and band automorphisms commute with every isomorphism (Olsson, Definition 31.1,
Remark 31.2, Lemma 31.3 and Remark 31.5).

## Main declarations

In the namespace `CategoryTheory.Pseudofunctor.BandedMorphism`:

* `fiberIsomActionFunctor`: the functor `X ↦ (y ≅ X_U x)` from `HomCategory bF bG` to `A(U)`-sets,
  with `fiberIsomActionFunctor_obj_V`, `fiberIsomActionFunctor_map_hom_apply` and
  `fiberIsomActionFunctor_map_homIso_inv`.
* `selfTransportActionIso`: transport along `e : x ≅ x'`, with
  `selfTransportActionIso_hom_hom`, `selfTransportActionIso_inv_hom`,
  `selfTransportActionIso_refl`, `selfTransportActionIso_trans` and
  `selfTransportActionIso_independent`.
* `selfTransportNatIso`: the natural transport, with `selfTransportNatIso_app`,
  `selfTransportNatIso_refl`, `selfTransportNatIso_trans` and
  `selfTransportNatIso_independent`.

## References

* [Martin Olsson, *Stacks* (lecture notes, notes by A. Geraschenko et al.)](https://stacky.net/files/written/Stacks/Stacks.pdf),
  Definition 31.1, Remark 31.2, Lemma 31.3 and Remark 31.5
-/

public section

universe w v u v' u'

open CategoryTheory Opposite Bicategory
open scoped Pseudofunctor.StrongTrans

namespace CategoryTheory.Pseudofunctor.BandedMorphism

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A : Sheaf J AddCommGrpCat.{w}}

section Functor

variable {F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  [∀ U : C, IsGroupoid (G.obj (.mk (op U)))] {bF : F.AbelianBanding J A}
  {bG : G.AbelianBanding J A}

variable (bF bG) in
/-- **The fibre action functor**: for objects `x` over `U` of `F` and `y` over `U` of `G`, the
functor from band-preserving transformations to `A(U)`-sets sending `X` to the isomorphisms
`y ≅ X_U x` and an arrow `m : X ⟶ Y` to postcomposition with its component `X_U x ≅ Y_U x`. -/
@[expose]
noncomputable def fiberIsomActionFunctor (U : C) (x : F.obj (.mk (op U)))
    (y : G.obj (.mk (op U))) :
    HomCategory bF bG ⥤ Action (Type v') (Multiplicative (A.obj.obj (op U))) where
  obj X := bG.fiberAction y ((X.obj.app (.mk (op U))).toFunctor.obj x)
  map m := (bG.postcomposeActionIso (componentIso m U x)).hom
  map_id X := by
    rw [componentIso_id, AbelianBanding.postcomposeActionIso_refl]
    rfl
  map_comp m n := by
    rw [componentIso_comp, AbelianBanding.postcomposeActionIso_trans]
    rfl

variable (bF bG) in
/-- The `A(U)`-set assigned to `X` by `fiberIsomActionFunctor` is the set of isomorphisms
`y ≅ X_U x`. -/
theorem fiberIsomActionFunctor_obj_V (U : C) (x : F.obj (.mk (op U))) (y : G.obj (.mk (op U)))
    (X : HomCategory bF bG) :
    ((fiberIsomActionFunctor bF bG U x y).obj X).V =
      (y ≅ (X.obj.app (.mk (op U))).toFunctor.obj x) :=
  (rfl)

/-- An arrow `m : X ⟶ Y` acts on `p : y ≅ X_U x` by postcomposition with its component. -/
@[simp]
theorem fiberIsomActionFunctor_map_hom_apply (U : C) (x : F.obj (.mk (op U)))
    (y : G.obj (.mk (op U))) {X Y : HomCategory bF bG} (m : X ⟶ Y)
    (p : y ≅ (X.obj.app (.mk (op U))).toFunctor.obj x) :
    ((fiberIsomActionFunctor bF bG U x y).map m).hom p = p ≪≫ componentIso m U x :=
  bG.postcomposeActionIso_hom_hom _ p

/-- The inverse `homIso m` of an arrow `m` acts by the inverse of postcomposition with the
component of `m`. -/
theorem fiberIsomActionFunctor_map_homIso_inv (U : C) (x : F.obj (.mk (op U)))
    (y : G.obj (.mk (op U))) {X Y : HomCategory bF bG} (m : X ⟶ Y) :
    (fiberIsomActionFunctor bF bG U x y).map (homIso m).inv =
      (bG.postcomposeActionIso (componentIso m U x)).inv := by
  -- The component of the inverse of `homIso m` is the inverse of the component of `m`.
  change (bG.postcomposeActionIso (componentIso (homIso m).inv U x)).hom = _
  rw [componentIso_homIso_inv, AbelianBanding.postcomposeActionIso_symm, Iso.symm_hom]

/-- The arrows of `fiberIsomActionFunctor` commute with the action of each coefficient. -/
theorem fiberIsomActionFunctor_map_comm (U : C) (x : F.obj (.mk (op U)))
    (y : G.obj (.mk (op U))) {X Y : HomCategory bF bG} (m : X ⟶ Y)
    (a : Multiplicative (A.obj.obj (op U))) :
    (((fiberIsomActionFunctor bF bG U x y).obj X).ρ a).asHom ≫
        ((fiberIsomActionFunctor bF bG U x y).map m).hom =
      ((fiberIsomActionFunctor bF bG U x y).map m).hom ≫
        (((fiberIsomActionFunctor bF bG U x y).obj Y).ρ a).asHom :=
  ((fiberIsomActionFunctor bF bG U x y).map m).comm a

end Functor

section Self

variable {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}} [∀ U : C, IsGroupoid (F.obj (.mk (op U)))]
  {b : F.AbelianBanding J A} {U : C} {x x' x'' : F.obj (.mk (op U))}

/-- **Self transport** along `e : x ≅ x'`: the isomorphism of `A(U)`-sets from `x ≅ X_U x` to
`x' ≅ X_U x'` sending `p` to `e⁻¹ ≫ p ≫ X_U e`, the composite of precomposition with `e⁻¹` and
postcomposition with `X_U e`. -/
noncomputable def selfTransportActionIso (X : HomCategory b b) (e : x ≅ x') :
    (fiberIsomActionFunctor b b U x x).obj X ≅ (fiberIsomActionFunctor b b U x' x').obj X :=
  b.precomposeActionIso e ≪≫
    b.postcomposeActionIso ((X.obj.app (.mk (op U))).toFunctor.mapIso e)

@[simp]
theorem selfTransportActionIso_hom_hom (X : HomCategory b b) (e : x ≅ x')
    (p : x ≅ (X.obj.app (.mk (op U))).toFunctor.obj x) :
    (selfTransportActionIso X e).hom.hom p =
      e.symm ≪≫ p ≪≫ (X.obj.app (.mk (op U))).toFunctor.mapIso e := by
  change (b.postcomposeActionIso _).hom.hom ((b.precomposeActionIso e).hom.hom p) = _
  rw [b.precomposeActionIso_hom_hom, b.postcomposeActionIso_hom_hom]
  exact Iso.trans_assoc _ _ _

@[simp]
theorem selfTransportActionIso_inv_hom (X : HomCategory b b) (e : x ≅ x')
    (p : x' ≅ (X.obj.app (.mk (op U))).toFunctor.obj x') :
    (selfTransportActionIso X e).inv.hom p =
      e ≪≫ p ≪≫ ((X.obj.app (.mk (op U))).toFunctor.mapIso e).symm := by
  change (b.precomposeActionIso e).inv.hom ((b.postcomposeActionIso _).inv.hom p) = _
  rw [b.postcomposeActionIso_inv_hom, b.precomposeActionIso_inv_hom]

/-- Transport along the identity is the identity. -/
@[simp]
theorem selfTransportActionIso_refl (X : HomCategory b b) :
    selfTransportActionIso X (Iso.refl x) = Iso.refl _ := by
  ext (p : x ≅ (X.obj.app (.mk (op U))).toFunctor.obj x)
  refine (selfTransportActionIso_hom_hom X _ p).trans ?_
  refine Iso.ext ?_
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.refl_inv, Functor.mapIso_refl, Iso.refl_hom,
    Category.comp_id, Category.id_comp]
  rfl

/-- Transport along `e ≪≫ f` is transport along `e` followed by transport along `f`. -/
theorem selfTransportActionIso_trans (X : HomCategory b b) (e : x ≅ x') (f : x' ≅ x'') :
    selfTransportActionIso X (e ≪≫ f) =
      selfTransportActionIso X e ≪≫ selfTransportActionIso X f := by
  ext (p : x ≅ (X.obj.app (.mk (op U))).toFunctor.obj x)
  refine (selfTransportActionIso_hom_hom X _ p).trans ?_
  change _ = (selfTransportActionIso X f).hom.hom ((selfTransportActionIso X e).hom.hom p)
  rw [selfTransportActionIso_hom_hom, selfTransportActionIso_hom_hom]
  refine Iso.ext ?_
  simp

/-- **Independence of the transport**: for a band-preserving `X`, transport along `e : x ≅ x'`
does not depend on `e`. The isomorphism `f` is `e` preceded by the band automorphism of a
coefficient `a` at `x`; `X_U` carries it to the band automorphism of `a` at `X_U x`, and band
automorphisms commute with every isomorphism. -/
theorem selfTransportActionIso_independent (X : HomCategory b b) (e f : x ≅ x') :
    selfTransportActionIso X e = selfTransportActionIso X f := by
  ext (p : x ≅ (X.obj.app (.mk (op U))).toFunctor.obj x)
  refine (selfTransportActionIso_hom_hom X e p).trans
    (Eq.trans ?_ (selfTransportActionIso_hom_hom X f p).symm)
  rw [← b.act_difference e f, AbelianBanding.act_eq_trans]
  refine Iso.ext ?_
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.trans_inv, Functor.map_comp,
    Category.assoc]
  rw [BandPreserving.map_mulEquiv_hom_assoc b X.obj, ← AbelianBanding.mulEquiv_hom_comp_assoc b p,
    Iso.inv_hom_id_assoc]

/-- **The natural self transport** along `e : x ≅ x'`: the natural isomorphism of fibre action
functors with components `selfTransportActionIso X e`. -/
noncomputable def selfTransportNatIso (e : x ≅ x') :
    fiberIsomActionFunctor b b U x x ≅ fiberIsomActionFunctor b b U x' x' :=
  NatIso.ofComponents (selfTransportActionIso · e) fun {X Y} m ↦ by
    ext (p : x ≅ (X.obj.app (.mk (op U))).toFunctor.obj x)
    change (selfTransportActionIso Y e).hom.hom
        (((fiberIsomActionFunctor b b U x x).map m).hom p) =
      ((fiberIsomActionFunctor b b U x' x').map m).hom ((selfTransportActionIso X e).hom.hom p)
    rw [fiberIsomActionFunctor_map_hom_apply, selfTransportActionIso_hom_hom,
      selfTransportActionIso_hom_hom, fiberIsomActionFunctor_map_hom_apply]
    refine Iso.ext ?_
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, componentIso_hom,
      Category.assoc]
    -- The component of `m` is natural in the fibre object.
    rw [(m.hom.as.app (.mk (op U))).toNatTrans.naturality e.hom]

@[simp]
theorem selfTransportNatIso_app (e : x ≅ x') (X : HomCategory b b) :
    (selfTransportNatIso e).app X = selfTransportActionIso X e :=
  (rfl)

/-- The natural transport is natural: arrows of the fibre action functors commute with it. -/
theorem selfTransportNatIso_naturality (e : x ≅ x') {X Y : HomCategory b b} (m : X ⟶ Y) :
    (fiberIsomActionFunctor b b U x x).map m ≫ (selfTransportActionIso Y e).hom =
      (selfTransportActionIso X e).hom ≫ (fiberIsomActionFunctor b b U x' x').map m :=
  (selfTransportNatIso e).hom.naturality m

/-- Natural transport along the identity is the identity. -/
@[simp]
theorem selfTransportNatIso_refl :
    selfTransportNatIso (b := b) (Iso.refl x) = Iso.refl _ :=
  Iso.ext (NatTrans.ext (funext fun X ↦ congrArg Iso.hom (selfTransportActionIso_refl X)))

/-- Natural transport along `e ≪≫ f` is natural transport along `e` followed by natural
transport along `f`. -/
theorem selfTransportNatIso_trans (e : x ≅ x') (f : x' ≅ x'') :
    selfTransportNatIso (b := b) (e ≪≫ f) = selfTransportNatIso e ≪≫ selfTransportNatIso f :=
  Iso.ext (NatTrans.ext (funext fun X ↦ congrArg Iso.hom (selfTransportActionIso_trans X e f)))

/-- The natural transport along `e : x ≅ x'` does not depend on `e`. -/
theorem selfTransportNatIso_independent (e f : x ≅ x') :
    selfTransportNatIso (b := b) e = selfTransportNatIso f :=
  Iso.ext (NatTrans.ext (funext fun X ↦
    congrArg Iso.hom (selfTransportActionIso_independent X e f)))

end Self

end CategoryTheory.Pseudofunctor.BandedMorphism
