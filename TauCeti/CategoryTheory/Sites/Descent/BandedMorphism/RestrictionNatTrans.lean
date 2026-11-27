/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Descent.BandedMorphism.FiberAction
public import TauCeti.CategoryTheory.Sites.Descent.BandedMorphism.Restriction

/-!
# Restriction of fibre isomorphisms as a natural transformation

Let `F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` carry `A`-bandings `bF`, `bG`, with groupoid fibres of
`G`, and let `f : V ⟶ U` be an arrow of `C`. For objects `x` of `F` and `y` of `G` over `U`, the
restrictions of fibre isomorphisms `BandedMorphism.fiberIsomRestriction f bG X x y` from
`y ≅ X_U x` to `G(f) y ≅ X_V (F(f) x)` are natural in the band-preserving transformation `X`: they
form a natural transformation `BandedMorphism.fiberIsomRestrictionNatTrans` from the fibre action
functor at `U` to the fibre action functor at `V`, with `A(U)` acting through `A(U) → A(V)`
(`Action.res`). Its naturality is the compatibility of the restriction comparisons with
modifications (`BandedMorphism.restrictionIso_modification`).

In the self case `F = G`, `bF = bG = b`, the restrictions commute with the self transport along an
isomorphism `e : x ≅ x'` and along its pullback `F(f) e`
(`BandedMorphism.selfTransportActionIso_restriction`), naturally in `X`
(`BandedMorphism.selfTransportNatIso_restriction`), by the naturality of the restriction
comparison in the object (`BandedMorphism.restrictionIso_naturality`) (Olsson, Definition 31.1,
Remarks 31.2 and 31.5; Groechenig, Wyss and Ziegler, Definition 2.6 and §2.2.1).

## Main declarations

In the namespace `CategoryTheory.Pseudofunctor.BandedMorphism`:

* `fiberIsomRestrictionNatTrans`, with `fiberIsomRestrictionNatTrans_app`;
* `selfTransportActionIso_restriction`, `selfTransportNatIso_restriction`.

## References

* [Martin Olsson, *Stacks* (lecture notes, notes by A. Geraschenko et al.)](https://stacky.net/files/written/Stacks/Stacks.pdf),
  Definition 31.1, Remark 31.2 and Remark 31.5
* [Michael Groechenig, Dimitri Wyss and Paul Ziegler, *Mirror symmetry for moduli of Higgs
  bundles via p-adic integration*](https://doi.org/10.1007/s00222-020-00957-8),
  Definition 2.6 and §2.2.1
-/

public section

universe w v u v' u'

open CategoryTheory Opposite Bicategory
open scoped Pseudofunctor.StrongTrans

namespace CategoryTheory.Pseudofunctor.BandedMorphism

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A : Sheaf J AddCommGrpCat.{w}} {U V : C} (f : V ⟶ U)

section Functor

variable {F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  [∀ U : C, IsGroupoid (G.obj (.mk (op U)))] (bF : F.AbelianBanding J A)
  (bG : G.AbelianBanding J A)

/-- **Restriction of fibre isomorphisms, naturally in the transformation.** For `f : V ⟶ U` and
objects `x` of `F` and `y` of `G` over `U`, the maps `fiberIsomRestriction f bG X x y` from
`y ≅ X_U x` to `G(f) y ≅ X_V (F(f) x)` form a natural transformation from the fibre action
functor at `U` to the fibre action functor at `V` followed by restriction of the action along
`A(U) → A(V)`. -/
noncomputable def fiberIsomRestrictionNatTrans (x : F.obj (.mk (op U)))
    (y : G.obj (.mk (op U))) :
    fiberIsomActionFunctor bF bG U x y ⟶
      fiberIsomActionFunctor bF bG V ((F.map f.op.toLoc).toFunctor.obj x)
          ((G.map f.op.toLoc).toFunctor.obj y) ⋙
        Action.res _ (AddMonoidHom.toMultiplicative (A.obj.map f.op).hom) where
  app X := fiberIsomRestriction f bG X.obj x y
  naturality {X Y} m := by
    ext (p : y ≅ (X.obj.app (.mk (op U))).toFunctor.obj x)
    -- The carriers of the fibre actions are the sets of isomorphisms only after unfolding
    -- `Action.ofMulAction`, so both sides are evaluated at `p` by chaining the evaluation
    -- lemmas with `Eq.trans`, as in `selfTransportNatIso`.
    refine (fiberIsomRestriction_hom_apply f bG Y.obj x
      (((fiberIsomActionFunctor bF bG U x y).map m).hom p)).trans (Eq.trans ?_
        (fiberIsomActionFunctor_map_hom_apply V _ _ m
          ((fiberIsomRestriction f bG X.obj x y).hom p)).symm)
    rw [fiberIsomActionFunctor_map_hom_apply, fiberIsomRestriction_hom_apply, Functor.mapIso_trans,
      Iso.trans_assoc, restrictionIso_modification, Iso.trans_assoc]

/-- The component of `fiberIsomRestrictionNatTrans` at `X` is `fiberIsomRestriction`. -/
@[simp]
theorem fiberIsomRestrictionNatTrans_app (x : F.obj (.mk (op U))) (y : G.obj (.mk (op U)))
    (X : HomCategory bF bG) :
    (fiberIsomRestrictionNatTrans f bF bG x y).app X = fiberIsomRestriction f bG X.obj x y :=
  (rfl)

end Functor

section Self

variable {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}} {b : F.AbelianBanding J A}
  {x x' : F.obj (.mk (op U))}

/-- **Self transport commutes with restriction.** For `e : x ≅ x'`, transporting along `e` and
then restricting along `f` is restricting along `f` and then transporting along the pullback
`F(f) e`. -/
@[reassoc]
theorem selfTransportActionIso_restriction (X : HomCategory b b) (e : x ≅ x') :
    (selfTransportActionIso X e).hom ≫ fiberIsomRestriction f b X.obj x' x' =
      fiberIsomRestriction f b X.obj x x ≫
        (Action.res _ (AddMonoidHom.toMultiplicative (A.obj.map f.op).hom)).map
          (selfTransportActionIso X ((F.map f.op.toLoc).toFunctor.mapIso e)).hom := by
  ext (p : x ≅ (X.obj.app (.mk (op U))).toFunctor.obj x)
  -- As in `fiberIsomRestrictionNatTrans`, both sides are evaluated at `p` by chaining the
  -- evaluation lemmas with `Eq.trans`.
  refine (fiberIsomRestriction_hom_apply f b X.obj x'
    ((selfTransportActionIso X e).hom.hom p)).trans (Eq.trans ?_ (selfTransportActionIso_hom_hom X _
      ((fiberIsomRestriction f b X.obj x x).hom p)).symm)
  rw [selfTransportActionIso_hom_hom, fiberIsomRestriction_hom_apply]
  refine Iso.ext ?_
  have h := congrArg Iso.hom (restrictionIso_naturality f X.obj e)
  simp only [Iso.trans_hom, Functor.mapIso_hom] at h
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv, Functor.map_comp,
    Category.assoc, h]

variable [∀ U : C, IsGroupoid (F.obj (.mk (op U)))]

/-- **Natural self transport commutes with restriction.** For `e : x ≅ x'`, the natural self
transport along `e` followed by the restriction transformation at `x'` is the restriction
transformation at `x` followed by the natural self transport along `F(f) e`, restricted along
`A(U) → A(V)`. -/
@[reassoc]
theorem selfTransportNatIso_restriction (e : x ≅ x') :
    (selfTransportNatIso e).hom ≫ fiberIsomRestrictionNatTrans f b b x' x' =
      fiberIsomRestrictionNatTrans f b b x x ≫
        Functor.whiskerRight (selfTransportNatIso ((F.map f.op.toLoc).toFunctor.mapIso e)).hom
          (Action.res _ (AddMonoidHom.toMultiplicative (A.obj.map f.op).hom)) := by
  refine NatTrans.ext (funext fun X ↦ ?_)
  simp only [NatTrans.comp_app, selfTransportNatIso_hom_app, fiberIsomRestrictionNatTrans_app,
    Functor.whiskerRight_app]
  exact selfTransportActionIso_restriction f X e

end Self

end CategoryTheory.Pseudofunctor.BandedMorphism
