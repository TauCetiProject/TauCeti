/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Descent.BandedMorphism.Fiber.HomSheaf
public import TauCeti.CategoryTheory.Sites.Descent.BandedMorphism.Restriction
public import TauCeti.CategoryTheory.Sites.Descent.IsomTorsor.Basic

/-!
# Base change of the fibre morphism sheaves

Let `F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` carry `A`-bandings `bF`, `bG`, let `G` be a prestack, and let
`X : F ⟶ G` be a band-preserving transformation. For `x` in the fibre of `F` and `y` in the fibre
of `G` over `U`, write `H_U(x, y; X) = G.sheafHom J y (X_U x)` on `(Over U, J.over U)`
(`BandedMorphism.fiberHomSheafFunctor`). Along `f : V ⟶ U`, the restriction of `H_U(x, y; X)` to
`Over V` is `H_V(F(f) x, G(f) y; X)` (`BandedMorphism.fiberHomBaseChangeIso`): Mathlib's
`Pseudofunctor.overMapCompPresheafHomIso` identifies the restriction with the sheaf of local
morphisms from `G(f) y` to `G(f) (X_U x)`, and the restriction comparison
`BandedMorphism.restrictionIso f X x : G(f) (X_U x) ≅ X_V (F(f) x)` identifies the target. On a
section `p` over `t ≫ f` the comparison is `k(y)⁻¹ ≫ p ≫ k(X_U x) ≫ G(t) (restrictionIso f X x)`,
where `k` is the composition isomorphism `G(t ≫ f) ≅ G(t) ∘ G(f)`
(`BandedMorphism.fiberHomBaseChangeIso_hom_app`, with the inverse in
`BandedMorphism.fiberHomBaseChangeIso_inv_app`). It commutes with modifications
(`BandedMorphism.fiberHomBaseChangeIso_modification`, from the tail formula
`BandedMorphism.mapComp'_hom_restrictionIso_hom_modification`), giving a
natural isomorphism of functors of `X` (`BandedMorphism.fiberHomBaseChangeNatIso`), and with the
action of the band on sections (`BandedMorphism.fiberHomBaseChangeIso_equivariant`) (Olsson,
Remark 31.5).

## Main declarations

In the namespace `CategoryTheory.Pseudofunctor.BandedMorphism`:

* `mapComp'_hom_restrictionIso_hom_modification`: modifications commute with the comparison
  `k(X_U x) ≫ G(t) (restrictionIso f X x)` after `p`.
* `fiberHomBaseChangeIso f x y X`, with `fiberHomBaseChangeIso_hom_app`,
  `fiberHomBaseChangeIso_inv_app`, `fiberHomBaseChangeIso_modification` and
  `fiberHomBaseChangeIso_equivariant`.
* `fiberHomBaseChangeNatIso f x y`, with `fiberHomBaseChangeNatIso_app`,
  `fiberHomBaseChangeNatIso_hom_app` and `fiberHomBaseChangeNatIso_inv_app`.

## References

* [Martin Olsson, *Stacks* (lecture notes, notes by A. Geraschenko et al.)](https://stacky.net/files/written/Stacks/Stacks.pdf),
  Remark 31.5
-/

public section

universe w v u v' u'

open CategoryTheory Opposite Bicategory
open scoped Pseudofunctor.StrongTrans

namespace CategoryTheory.Pseudofunctor.BandedMorphism

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A : Sheaf J AddCommGrpCat.{w}} {F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  {bF : F.AbelianBanding J A} {bG : G.AbelianBanding J A}
  {U V : C} (f : V ⟶ U) (x : F.obj (.mk (op U))) (y : G.obj (.mk (op U)))

/-- **Modifications commute with the comparison after a section**: for `m : X ⟶ Y` and
`t : W ⟶ V`, pulling back `m_U x` along `t ≫ f` and then applying `k(Y_U x)` and
`G(t) (restrictionIso f Y x)` is applying `k(X_U x)` and `G(t) (restrictionIso f X x)` and then
pulling back `m_V (F(f) x)` along `t`, where `k` is the composition isomorphism
`G(t ≫ f) ≅ G(t) ∘ G(f)`. -/
@[reassoc]
theorem mapComp'_hom_restrictionIso_hom_modification {W : C} (t : W ⟶ V)
    {X Y : HomCategory bF bG} (m : X ⟶ Y) :
    (G.map (t ≫ f).op.toLoc).toFunctor.map ((m.hom.as.app (.mk (op U))).toNatTrans.app x) ≫
        (G.mapComp' f.op.toLoc t.op.toLoc (t ≫ f).op.toLoc).hom.toNatTrans.app
          ((Y.obj.app (.mk (op U))).toFunctor.obj x) ≫
        (G.map t.op.toLoc).toFunctor.map (restrictionIso f Y.obj x).hom =
      (G.mapComp' f.op.toLoc t.op.toLoc (t ≫ f).op.toLoc).hom.toNatTrans.app
          ((X.obj.app (.mk (op U))).toFunctor.obj x) ≫
        (G.map t.op.toLoc).toFunctor.map (restrictionIso f X.obj x).hom ≫
        (G.map t.op.toLoc).toFunctor.map
          ((m.hom.as.app (.mk (op V))).toNatTrans.app ((F.map f.op.toLoc).toFunctor.obj x)) := by
  rw [reassoc_of% (G.mapComp' f.op.toLoc t.op.toLoc (t ≫ f).op.toLoc).hom.toNatTrans.naturality]
  simp only [Cat.Hom.comp_toFunctor, Functor.comp_map, ← Functor.map_comp,
    restrictionIso_hom_modification]

variable [G.IsPrestack J]

/-- **Base change of the fibre morphism sheaf** along `f : V ⟶ U`: the restriction of
`H_U(x, y; X) = G.sheafHom J y (X_U x)` to `Over V` is `H_V(F(f) x, G(f) y; X)`, by Mathlib's
`overMapCompPresheafHomIso` followed by postcomposition with the restriction comparison
`restrictionIso f X x`. -/
noncomputable def fiberHomBaseChangeIso (X : HomCategory bF bG) :
    (J.overMapPullback (Type v') f).obj ((fiberHomSheafFunctor bF bG J U x y).obj X) ≅
      (fiberHomSheafFunctor bF bG J V ((F.map f.op.toLoc).toFunctor.obj x)
        ((G.map f.op.toLoc).toFunctor.obj y)).obj X :=
  (fullyFaithfulSheafToPresheaf (J.over V) (Type v')).preimageIso
    (Y := G.sheafHom J ((G.map f.op.toLoc).toFunctor.obj y)
      ((G.map f.op.toLoc).toFunctor.obj ((X.obj.app (.mk (op U))).toFunctor.obj x)))
    (G.overMapCompPresheafHomIso y ((X.obj.app (.mk (op U))).toFunctor.obj x) f) ≪≫
    (G.sheafHomFunctor J ((G.map f.op.toLoc).toFunctor.obj y)).mapIso (restrictionIso f X.obj x)

/-- **The section formula of the base change**: a section `p` over `t ≫ f` goes to
`k(y)⁻¹ ≫ p ≫ k(X_U x) ≫ G(t) (restrictionIso f X x)`, where `k` is the composition isomorphism
`G(t ≫ f) ≅ G(t) ∘ G(f)`. -/
theorem fiberHomBaseChangeIso_hom_app (X : HomCategory bF bG) (T : (Over V)ᵒᵖ)
    (p : ((fiberHomSheafFunctor bF bG J U x y).obj X).obj.obj (op ((Over.map f).obj T.unop))) :
    (fiberHomBaseChangeIso f x y X).hom.hom.app T p =
      (G.mapComp' f.op.toLoc T.unop.hom.op.toLoc
          ((Over.map f).obj T.unop).hom.op.toLoc).inv.toNatTrans.app y ≫ p ≫
        (G.mapComp' f.op.toLoc T.unop.hom.op.toLoc
          ((Over.map f).obj T.unop).hom.op.toLoc).hom.toNatTrans.app
            ((X.obj.app (.mk (op U))).toFunctor.obj x) ≫
        (G.map T.unop.hom.op.toLoc).toFunctor.map (restrictionIso f X.obj x).hom := by
  -- The source of `overMapCompPresheafHomIso` is the restricted sheaf only up to unfolding
  -- `overMapPullback`, so `Iso.trans_hom` and `preimageIso_hom` do not rewrite the sheaf
  -- morphism; `change` states its presheaf components.
  change (G.presheafHomPostcomp _ (restrictionIso f X.obj x).hom).app T
    ((G.overMapCompPresheafHomIso y _ f).hom.app T p) = _
  rw [presheafHomPostcomp_app_apply]
  -- `p` is a morphism in the fibre over `((Over.map f).obj T.unop).left`, which is the fibre over
  -- `T.unop.left` only up to unfolding `Over.map`. So neither `rw`/`simp only` with
  -- `overMapCompPresheafHomIso_hom_app` and `Category.assoc` matches, and `erw` unfolds
  -- `mapComp'`; the rewrite and the associativity steps are given as terms.
  exact (congrArg (· ≫ _) (G.overMapCompPresheafHomIso_hom_app y _ f T p)).trans <|
    (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _))

/-- **The section formula of the inverse base change**: a section `q` over `t` goes to
`k(y) ≫ q ≫ G(t) (restrictionIso f X x)⁻¹ ≫ k(X_U x)⁻¹`, where `k` is the composition
isomorphism `G(t ≫ f) ≅ G(t) ∘ G(f)`. -/
theorem fiberHomBaseChangeIso_inv_app (X : HomCategory bF bG) (T : (Over V)ᵒᵖ)
    (q : ((fiberHomSheafFunctor bF bG J V ((F.map f.op.toLoc).toFunctor.obj x)
        ((G.map f.op.toLoc).toFunctor.obj y)).obj X).obj.obj T) :
    (fiberHomBaseChangeIso f x y X).inv.hom.app T q =
      (G.mapComp' f.op.toLoc T.unop.hom.op.toLoc
          ((Over.map f).obj T.unop).hom.op.toLoc).hom.toNatTrans.app y ≫ q ≫
        (G.map T.unop.hom.op.toLoc).toFunctor.map (restrictionIso f X.obj x).inv ≫
        (G.mapComp' f.op.toLoc T.unop.hom.op.toLoc
          ((Over.map f).obj T.unop).hom.op.toLoc).inv.toNatTrans.app
            ((X.obj.app (.mk (op U))).toFunctor.obj x) := by
  -- As in `fiberHomBaseChangeIso_hom_app`, `change` states the presheaf components.
  change (G.overMapCompPresheafHomIso y _ f).inv.app T
    ((G.presheafHomPostcomp _ (restrictionIso f X.obj x).inv).app T q) = _
  rw [overMapCompPresheafHomIso_inv_app]
  -- As in `fiberHomBaseChangeIso_hom_app`, `presheafHomPostcomp_app_apply` and `Category.assoc`
  -- do not rewrite, because the fibre containing `q` matches only up to unfolding `Over.map`.
  exact congrArg (_ ≫ ·) ((congrArg (· ≫ _) (G.presheafHomPostcomp_app_apply _ _ T q)).trans
    (Category.assoc _ _ _))

/-- **Base change commutes with modifications**: for `m : X ⟶ Y`, restricting the action of `m`
on `H_U` and comparing with `Y` is comparing with `X` and then acting by `m` on `H_V`. -/
@[reassoc]
theorem fiberHomBaseChangeIso_modification {X Y : HomCategory bF bG} (m : X ⟶ Y) :
    (J.overMapPullback (Type v') f).map ((fiberHomSheafFunctor bF bG J U x y).map m) ≫
        (fiberHomBaseChangeIso f x y Y).hom =
      (fiberHomBaseChangeIso f x y X).hom ≫
        (fiberHomSheafFunctor bF bG J V ((F.map f.op.toLoc).toFunctor.obj x)
          ((G.map f.op.toLoc).toFunctor.obj y)).map m := by
  apply Sheaf.hom_ext
  ext T p
  -- A composite of sheaf morphisms applied to a section is the nested application by definition;
  -- the `Sheaf` and `Type` composition lemmas do not rewrite here, because the sections are hom
  -- types only up to unfolding.
  change (fiberHomBaseChangeIso f x y Y).hom.hom.app T
      (((fiberHomSheafFunctor bF bG J U x y).map m).hom.app _ p) =
    ((fiberHomSheafFunctor bF bG J V _ _).map m).hom.app T
      ((fiberHomBaseChangeIso f x y X).hom.hom.app T p)
  refine (fiberHomBaseChangeIso_hom_app f x y Y T _).trans (Eq.trans ?_
    (fiberHomSheafFunctor_map_hom_app _ _ m T _).symm)
  -- `erw`: the sections of the fibre morphism sheaves are hom types only up to unfolding.
  erw [fiberHomSheafFunctor_map_hom_app, fiberHomBaseChangeIso_hom_app]
  -- Both sides are `k(y)⁻¹ ≫ p ≫ _`; compare the tails after `p`. As in
  -- `fiberHomBaseChangeIso_hom_app`, `Category.assoc` and the `_assoc` form of the tail lemma
  -- do not rewrite around `p`, whose fibre matches only up to unfolding `Over.map`.
  exact (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans <|
    (congrArg (p ≫ ·) (mapComp'_hom_restrictionIso_hom_modification f x T.unop.hom m)).trans <|
      (congrArg (p ≫ ·) (Category.assoc _ _ _).symm).trans (Category.assoc _ _ _).symm)).trans
    (Category.assoc _ _ _).symm

/-- **Base change commutes with the action of the band**: for a section `p` over `t ≫ f` and
`a ∈ A(T)`, the comparison carries `p` acted on by `a` to its image acted on by the same `a`. -/
theorem fiberHomBaseChangeIso_equivariant (X : HomCategory bF bG) (T : (Over V)ᵒᵖ)
    (p : (G.presheafHom y ((componentFunctor bF bG U x).obj X)).obj
      (op ((Over.map f).obj T.unop)))
    (a : Multiplicative (A.obj.obj (op T.unop.left))) :
    (fiberHomBaseChangeIso f x y X).hom.hom.app T (bG.homAct p a) =
      bG.homAct ((fiberHomBaseChangeIso f x y X).hom.hom.app T p) a := by
  -- As in `fiberHomBaseChangeIso_hom_app`, `change` states the presheaf components.
  change (G.presheafHomPostcomp _ (restrictionIso f X.obj x).hom).app T
      ((G.overMapCompPresheafHomIso y _ f).hom.app T (bG.homAct p a)) =
    bG.homAct ((G.presheafHomPostcomp _ (restrictionIso f X.obj x).hom).app T
      ((G.overMapCompPresheafHomIso y _ f).hom.app T p)) a
  rw [presheafHomPostcomp_app_apply, presheafHomPostcomp_app_apply]
  exact (congrArg (· ≫ _) (bG.overMapCompPresheafHomIso_hom_app_homAct f T p a)).trans
    (bG.homAct_comp_hom _
      ((G.map T.unop.hom.op.toLoc).toFunctor.mapIso (restrictionIso f X.obj x)) a)

/-- **The base change comparisons form a natural isomorphism** between the functors
`X ↦ f^* H_U(x, y; X)` and `X ↦ H_V(F(f) x, G(f) y; X)` of the band-preserving transformation. -/
noncomputable def fiberHomBaseChangeNatIso :
    fiberHomSheafFunctor bF bG J U x y ⋙ J.overMapPullback (Type v') f ≅
      fiberHomSheafFunctor bF bG J V ((F.map f.op.toLoc).toFunctor.obj x)
        ((G.map f.op.toLoc).toFunctor.obj y) :=
  NatIso.ofComponents (fun X ↦ fiberHomBaseChangeIso f x y X)
    (fun m ↦ fiberHomBaseChangeIso_modification f x y m)

@[simp]
theorem fiberHomBaseChangeNatIso_app (X : HomCategory bF bG) :
    (fiberHomBaseChangeNatIso (bF := bF) (bG := bG) f x y).app X = fiberHomBaseChangeIso f x y X :=
  NatIso.ofComponents.app _ _ X

@[simp]
theorem fiberHomBaseChangeNatIso_hom_app (X : HomCategory bF bG) :
    (fiberHomBaseChangeNatIso (bF := bF) (bG := bG) f x y).hom.app X =
      (fiberHomBaseChangeIso f x y X).hom := by
  rw [← Iso.app_hom, fiberHomBaseChangeNatIso_app]

@[simp]
theorem fiberHomBaseChangeNatIso_inv_app (X : HomCategory bF bG) :
    (fiberHomBaseChangeNatIso (bF := bF) (bG := bG) f x y).inv.app X =
      (fiberHomBaseChangeIso f x y X).inv := by
  rw [← Iso.app_inv, fiberHomBaseChangeNatIso_app]

end CategoryTheory.Pseudofunctor.BandedMorphism
