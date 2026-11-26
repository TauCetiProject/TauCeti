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
  with `fiberIsomActionFunctor_obj`, `fiberIsomActionFunctor_obj_V`,
  `fiberIsomActionFunctor_map`, `fiberIsomActionFunctor_map_hom_apply` and
  `fiberIsomActionFunctor_map_homIso_inv`.
* `selfTransportActionIso`: transport along `e : x ≅ x'`, with
  `selfTransportActionIso_hom_hom`, `selfTransportActionIso_inv_hom`,
  `selfTransportActionIso_refl`, `selfTransportActionIso_trans` and
  `selfTransportActionIso_independent`.
* `selfTransportNatIso`: the natural transport, with `selfTransportNatIso_app`,
  `selfTransportNatIso_hom_app`, `selfTransportNatIso_inv_app`, `selfTransportNatIso_refl`,
  `selfTransportNatIso_trans` and `selfTransportNatIso_independent`.

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
    -- `𝟙` of the object `bG.fiberAction y (X_U x)` is by definition `𝟙` of `obj X`.
    exact Iso.refl_hom _
  map_comp m n := by
    rw [componentIso_comp, AbelianBanding.postcomposeActionIso_trans]
    -- The `fiberAction` objects in this composite are by definition the objects `obj X`,
    -- `obj Y` and `obj Z` of the functor being defined.
    exact Iso.trans_hom _ _

variable (bF bG) in
/-- `fiberIsomActionFunctor` sends `X` to the `A(U)`-set `y ≅ X_U x`. -/
theorem fiberIsomActionFunctor_obj (U : C) (x : F.obj (.mk (op U))) (y : G.obj (.mk (op U)))
    (X : HomCategory bF bG) :
    (fiberIsomActionFunctor bF bG U x y).obj X =
      bG.fiberAction y ((X.obj.app (.mk (op U))).toFunctor.obj x) :=
  (rfl)

variable (bF bG) in
/-- The `A(U)`-set assigned to `X` by `fiberIsomActionFunctor` is the set of isomorphisms
`y ≅ X_U x`. -/
theorem fiberIsomActionFunctor_obj_V (U : C) (x : F.obj (.mk (op U))) (y : G.obj (.mk (op U)))
    (X : HomCategory bF bG) :
    ((fiberIsomActionFunctor bF bG U x y).obj X).V =
      (y ≅ (X.obj.app (.mk (op U))).toFunctor.obj x) :=
  (rfl)

/-- `fiberIsomActionFunctor` sends an arrow `m : X ⟶ Y` to postcomposition with its component
`X_U x ≅ Y_U x`. -/
theorem fiberIsomActionFunctor_map (U : C) (x : F.obj (.mk (op U))) (y : G.obj (.mk (op U)))
    {X Y : HomCategory bF bG} (m : X ⟶ Y) :
    (fiberIsomActionFunctor bF bG U x y).map m =
      (bG.postcomposeActionIso (componentIso m U x)).hom :=
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
  rw [fiberIsomActionFunctor_map, componentIso_homIso_inv,
    AbelianBanding.postcomposeActionIso_symm, Iso.symm_hom]

end Functor

section Self

variable {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}} {b : F.AbelianBanding J A} {U : C}
  {x x' x'' : F.obj (.mk (op U))}

/-- **Self transport** along `e : x ≅ x'`: the isomorphism of `A(U)`-sets from `x ≅ X_U x` to
`x' ≅ X_U x'` sending `p` to `e⁻¹ ≫ p ≫ X_U e`, the composite of precomposition with `e⁻¹` and
postcomposition with `X_U e`. When the fibres are groupoids, its source and target are the
objects `(fiberIsomActionFunctor b b U x x).obj X` and `(fiberIsomActionFunctor b b U x' x').obj X`
(`fiberIsomActionFunctor_obj`). -/
noncomputable def selfTransportActionIso (X : HomCategory b b) (e : x ≅ x') :
    b.fiberAction x ((X.obj.app (.mk (op U))).toFunctor.obj x) ≅
      b.fiberAction x' ((X.obj.app (.mk (op U))).toFunctor.obj x') :=
  b.precomposeActionIso e ≪≫
    b.postcomposeActionIso ((X.obj.app (.mk (op U))).toFunctor.mapIso e)

@[simp]
theorem selfTransportActionIso_hom_hom (X : HomCategory b b) (e : x ≅ x')
    (p : x ≅ (X.obj.app (.mk (op U))).toFunctor.obj x) :
    (selfTransportActionIso X e).hom.hom p =
      e.symm ≪≫ p ≪≫ (X.obj.app (.mk (op U))).toFunctor.mapIso e := by
  -- The carrier of `fiberAction` is `x ≅ y` only after unfolding `Action.ofMulAction`, so `rw`
  -- and `simp` cannot evaluate the composite `Action.comp_hom` at the isomorphism `p`. By
  -- definition the composite applied to `p` is postcomposition applied to the precomposition of
  -- `p`, so the two evaluation lemmas are chained by `Eq.trans`.
  refine (b.postcomposeActionIso_hom_hom _ ((b.precomposeActionIso e).hom.hom p)).trans ?_
  rw [b.precomposeActionIso_hom_hom, Iso.trans_assoc]

@[simp]
theorem selfTransportActionIso_inv_hom (X : HomCategory b b) (e : x ≅ x')
    (p : x' ≅ (X.obj.app (.mk (op U))).toFunctor.obj x') :
    (selfTransportActionIso X e).inv.hom p =
      e ≪≫ p ≪≫ ((X.obj.app (.mk (op U))).toFunctor.mapIso e).symm := by
  -- As in `selfTransportActionIso_hom_hom`, the evaluation lemmas are chained by `Eq.trans`.
  exact (b.precomposeActionIso_inv_hom e ((b.postcomposeActionIso _).inv.hom p)).trans
    (congrArg (e ≪≫ ·) (b.postcomposeActionIso_inv_hom _ p))

/-- Transport along the identity is the identity. -/
@[simp]
theorem selfTransportActionIso_refl (X : HomCategory b b) :
    selfTransportActionIso X (Iso.refl x) = Iso.refl _ := by
  simp only [selfTransportActionIso, AbelianBanding.precomposeActionIso_refl,
    Functor.mapIso_refl, AbelianBanding.postcomposeActionIso_refl, Iso.refl_trans]

/-- Transport along `e ≪≫ f` is transport along `e` followed by transport along `f`. -/
@[simp]
theorem selfTransportActionIso_trans (X : HomCategory b b) (e : x ≅ x') (f : x' ≅ x'') :
    selfTransportActionIso X (e ≪≫ f) =
      selfTransportActionIso X e ≪≫ selfTransportActionIso X f := by
  ext (p : x ≅ (X.obj.app (.mk (op U))).toFunctor.obj x)
  -- As in `selfTransportActionIso_hom_hom`, the composite of the two transports applied to `p`
  -- is evaluated by chaining `selfTransportActionIso_hom_hom` with `Eq.trans`.
  refine (selfTransportActionIso_hom_hom X _ p).trans (Eq.trans ?_
    (selfTransportActionIso_hom_hom X f ((selfTransportActionIso X e).hom.hom p)).symm)
  rw [selfTransportActionIso_hom_hom]
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

variable [∀ U : C, IsGroupoid (F.obj (.mk (op U)))]

/-- **The natural self transport** along `e : x ≅ x'`: the natural isomorphism of fibre action
functors with components `selfTransportActionIso X e`. -/
noncomputable def selfTransportNatIso (e : x ≅ x') :
    fiberIsomActionFunctor b b U x x ≅ fiberIsomActionFunctor b b U x' x' :=
  NatIso.ofComponents (selfTransportActionIso · e) fun {X Y} m ↦ by
    ext (p : x ≅ (X.obj.app (.mk (op U))).toFunctor.obj x)
    -- As in `selfTransportActionIso_hom_hom`, both sides of the naturality square are evaluated
    -- at `p` by chaining the evaluation lemmas with `Eq.trans`.
    refine (selfTransportActionIso_hom_hom Y e
      (((fiberIsomActionFunctor b b U x x).map m).hom p)).trans (Eq.trans ?_
        (fiberIsomActionFunctor_map_hom_apply U x' x' m
          ((selfTransportActionIso X e).hom.hom p)).symm)
    rw [fiberIsomActionFunctor_map_hom_apply, selfTransportActionIso_hom_hom]
    refine Iso.ext ?_
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, componentIso_hom,
      Category.assoc]
    -- The component of `m` is natural in the fibre object.
    rw [(m.hom.as.app (.mk (op U))).toNatTrans.naturality e.hom]

@[simp]
theorem selfTransportNatIso_app (e : x ≅ x') (X : HomCategory b b) :
    (selfTransportNatIso e).app X = selfTransportActionIso X e :=
  (rfl)

/-- The forward component of `selfTransportNatIso e` at `X` is that of
`selfTransportActionIso X e`. -/
@[simp]
theorem selfTransportNatIso_hom_app (e : x ≅ x') (X : HomCategory b b) :
    (selfTransportNatIso e).hom.app X = (selfTransportActionIso X e).hom :=
  (rfl)

/-- The inverse component of `selfTransportNatIso e` at `X` is that of
`selfTransportActionIso X e`. -/
@[simp]
theorem selfTransportNatIso_inv_app (e : x ≅ x') (X : HomCategory b b) :
    (selfTransportNatIso e).inv.app X = (selfTransportActionIso X e).inv :=
  (rfl)

/-- Natural transport along the identity is the identity. -/
@[simp]
theorem selfTransportNatIso_refl :
    selfTransportNatIso (b := b) (Iso.refl x) = Iso.refl _ :=
  Iso.ext (NatTrans.ext (funext fun X ↦ congrArg Iso.hom (selfTransportActionIso_refl X)))

/-- Natural transport along `e ≪≫ f` is natural transport along `e` followed by natural
transport along `f`. -/
@[simp]
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
