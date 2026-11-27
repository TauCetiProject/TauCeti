/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Descent.BandedMorphism.FiberHomSheaf
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
(`BandedMorphism.fiberHomBaseChangeIso_hom_app`). It commutes with modifications, giving a
natural isomorphism of functors of `X` (`BandedMorphism.fiberHomBaseChangeNatIso`), and with the
action of the band on sections (`BandedMorphism.fiberHomBaseChangeIso_equivariant`) (Olsson,
Remark 31.5).

## Main declarations

In the namespace `CategoryTheory.Pseudofunctor.BandedMorphism`:

* `fiberHomBaseChangeIso f x y X`, with `fiberHomBaseChangeIso_hom_app`,
  `fiberHomBaseChangeIso_modification` and `fiberHomBaseChangeIso_equivariant`.
* `fiberHomBaseChangeNatIso f x y`, with `fiberHomBaseChangeNatIso_app`.

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
  {bF : F.AbelianBanding J A} {bG : G.AbelianBanding J A} [G.IsPrestack J]
  {U V : C} (f : V ⟶ U) (x : F.obj (.mk (op U))) (y : G.obj (.mk (op U)))

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
  change (G.presheafHomPostcomp _ (restrictionIso f X.obj x).hom).app T
    ((G.overMapCompPresheafHomIso y _ f).hom.app T p) = _
  rw [presheafHomPostcomp_app_apply]
  dsimp [overMapCompPresheafHomIso]
  exact (Category.assoc _ _ _).trans (Category.assoc _ _ _)

/-- **Base change commutes with modifications**: for `m : X ⟶ Y`, restricting the action of `m`
on `H_U` and comparing with `Y` is comparing with `X` and then acting by `m` on `H_V`. -/
theorem fiberHomBaseChangeIso_modification [∀ U : C, IsGroupoid (G.obj (.mk (op U)))]
    {X Y : HomCategory bF bG} (m : X ⟶ Y) :
    (J.overMapPullback (Type v') f).map ((fiberHomSheafFunctor bF bG J U x y).map m) ≫
        (fiberHomBaseChangeIso f x y Y).hom =
      (fiberHomBaseChangeIso f x y X).hom ≫
        (fiberHomSheafFunctor bF bG J V ((F.map f.op.toLoc).toFunctor.obj x)
          ((G.map f.op.toLoc).toFunctor.obj y)).map m := by
  apply Sheaf.hom_ext
  ext T p
  have h := congrArg Iso.hom (restrictionIso_modification f m x)
  simp only [Iso.trans_hom, Functor.mapIso_hom, componentIso_hom] at h
  have hk := (G.mapComp' f.op.toLoc T.unop.hom.op.toLoc
    ((Over.map f).obj T.unop).hom.op.toLoc).hom.toNatTrans.naturality
      ((m.hom.as.app (.mk (op U))).toNatTrans.app x)
  change (fiberHomBaseChangeIso f x y Y).hom.hom.app T
      (((fiberHomSheafFunctor bF bG J U x y).map m).hom.app _ p) =
    ((fiberHomSheafFunctor bF bG J V _ _).map m).hom.app T
      ((fiberHomBaseChangeIso f x y X).hom.hom.app T p)
  refine (fiberHomBaseChangeIso_hom_app f x y Y T _).trans (Eq.trans ?_
    (fiberHomSheafFunctor_map_hom_app _ _ m T _).symm)
  -- `erw`: the sections of the fibre morphism sheaves are hom types only up to unfolding.
  erw [fiberHomSheafFunctor_map_hom_app, fiberHomBaseChangeIso_hom_app]
  -- Compare the tails after `p`, by naturality of the composition isomorphism and `h`.
  have key : ∀ q : (G.map ((Over.map f).obj T.unop).hom.op.toLoc).toFunctor.obj y ⟶
      (G.map ((Over.map f).obj T.unop).hom.op.toLoc).toFunctor.obj
        ((X.obj.app (.mk (op U))).toFunctor.obj x),
      (q ≫ (G.map ((Over.map f).obj T.unop).hom.op.toLoc).toFunctor.map
          ((m.hom.as.app (.mk (op U))).toNatTrans.app x)) ≫
        (G.mapComp' f.op.toLoc T.unop.hom.op.toLoc
          ((Over.map f).obj T.unop).hom.op.toLoc).hom.toNatTrans.app
            ((Y.obj.app (.mk (op U))).toFunctor.obj x) ≫
        (G.map T.unop.hom.op.toLoc).toFunctor.map (restrictionIso f Y.obj x).hom =
      (q ≫ (G.mapComp' f.op.toLoc T.unop.hom.op.toLoc
          ((Over.map f).obj T.unop).hom.op.toLoc).hom.toNatTrans.app
            ((X.obj.app (.mk (op U))).toFunctor.obj x) ≫
        (G.map T.unop.hom.op.toLoc).toFunctor.map (restrictionIso f X.obj x).hom) ≫
        (G.map T.unop.hom.op.toLoc).toFunctor.map
          ((m.hom.as.app (.mk (op V))).toNatTrans.app ((F.map f.op.toLoc).toFunctor.obj x)) := by
    intro q
    simp only [Category.assoc]
    rw [reassoc_of% hk]
    simp only [Cat.Hom.comp_toFunctor, Functor.comp_map, ← Functor.map_comp, h]
  exact (congrArg (_ ≫ ·) (key p)).trans (Category.assoc _ _ _).symm

/-- **Base change commutes with the action of the band**: for a section `p` over `t ≫ f` and
`a ∈ A(T)`, the comparison carries `p` acted on by `a` to its image acted on by the same `a`. -/
theorem fiberHomBaseChangeIso_equivariant (X : HomCategory bF bG) (T : (Over V)ᵒᵖ)
    (p : (G.presheafHom y ((componentFunctor bF bG U x).obj X)).obj
      (op ((Over.map f).obj T.unop)))
    (a : Multiplicative (A.obj.obj (op T.unop.left))) :
    (fiberHomBaseChangeIso f x y X).hom.hom.app T (bG.homAct p a) =
      bG.homAct ((fiberHomBaseChangeIso f x y X).hom.hom.app T p) a :=
  -- Both comparison factors after `p` form an isomorphism, and the one before it is
  -- precomposition.
  (fiberHomBaseChangeIso_hom_app f x y X T _).trans <|
    (congrArg (_ ≫ ·) (bG.homAct_comp_hom p
      ((Cat.Hom.toNatIso (G.mapComp' f.op.toLoc T.unop.hom.op.toLoc
          ((Over.map f).obj T.unop).hom.op.toLoc)).app
          ((X.obj.app (.mk (op U))).toFunctor.obj x) ≪≫
        (G.map T.unop.hom.op.toLoc).toFunctor.mapIso (restrictionIso f X.obj x)) a)).trans <|
    (bG.comp_homAct _ _ a).trans
      (congrArg (bG.homAct · a) (fiberHomBaseChangeIso_hom_app f x y X T p).symm)

/-- **The base change comparisons form a natural isomorphism** between the functors
`X ↦ f^* H_U(x, y; X)` and `X ↦ H_V(F(f) x, G(f) y; X)` of the band-preserving transformation. -/
noncomputable def fiberHomBaseChangeNatIso [∀ U : C, IsGroupoid (G.obj (.mk (op U)))] :
    fiberHomSheafFunctor bF bG J U x y ⋙ J.overMapPullback (Type v') f ≅
      fiberHomSheafFunctor bF bG J V ((F.map f.op.toLoc).toFunctor.obj x)
        ((G.map f.op.toLoc).toFunctor.obj y) :=
  NatIso.ofComponents (fun X ↦ fiberHomBaseChangeIso f x y X)
    (fun m ↦ fiberHomBaseChangeIso_modification f x y m)

@[simp]
theorem fiberHomBaseChangeNatIso_app [∀ U : C, IsGroupoid (G.obj (.mk (op U)))]
    (X : HomCategory bF bG) :
    (fiberHomBaseChangeNatIso (bF := bF) (bG := bG) f x y).app X = fiberHomBaseChangeIso f x y X :=
  NatIso.ofComponents.app _ _ X

end CategoryTheory.Pseudofunctor.BandedMorphism
