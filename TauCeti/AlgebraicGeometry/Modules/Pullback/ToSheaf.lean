/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Adjunction.Mates
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Basic
public import TauCeti.AlgebraicGeometry.Modules.Sheaf
public import TauCeti.CategoryTheory.Sites.Pullback
public import TauCeti.Topology.Sheaves.Functors

/-!
# Pullback of modules and inverse image of the underlying abelian sheaves

Let `g : Y ⟶ X` be a morphism of schemes and `M` a sheaf of modules on `X`. Pushforward of
sheaves of modules along `g` and pushforward of abelian sheaves along `g` agree on underlying
abelian sheaves. Taking mates under the two pullback--pushforward adjunctions gives a comparison
`g⁻¹ M ⟶ g^* M` from the inverse image of the underlying abelian sheaf of `M` to the underlying
abelian sheaf of the module pullback, natural in `M`.

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.toSheafPullbackComparison`: the comparison `g⁻¹ M ⟶ g^* M`;
* `AlgebraicGeometry.Scheme.Hom.toSheafPullbackComparison_unit`: the unit of the module pullback
  is the unit of the abelian inverse image followed by the comparison;
* `AlgebraicGeometry.Scheme.Hom.toSheafPullbackComparison_comp`: the comparison for `a ≫ b` is the
  comparison for `b` followed by that for `a` and `Scheme.Modules.pullbackComp`.
-/

public section

open CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (g : Y ⟶ X)

/-- The comparison `g⁻¹ M ⟶ g^* M` from the inverse image of the underlying abelian sheaf of `M`
to the underlying abelian sheaf of its pullback as a sheaf of modules: the mate of the equality of
the underlying abelian sheaves of `g_* N` computed in both ways. -/
def toSheafPullbackComparison :
    toSheaf X ⋙ (Opens.map g.base).sheafPullback AddCommGrpCat.{u}
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) ⟶
      Scheme.Modules.pullback g ⋙ toSheaf Y :=
  (mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction g)
    ((Opens.map g.base).sheafAdjunctionContinuous AddCommGrpCat.{u} _ _)).symm (𝟙 _)

/-- On sections, the unit of the module pullback is the abelian unit followed by the comparison
`g⁻¹ M ⟶ g^* M`. -/
lemma toSheafPullbackComparison_unit (M : X.Modules) :
    (toSheaf X).map ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M) =
      ((Opens.map g.base).sheafAdjunctionContinuous AddCommGrpCat.{u}
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).unit.app
          ((toSheaf X).obj M) ≫
        ((Opens.map g.base).sheafPushforwardContinuous AddCommGrpCat.{u}
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).map
          ((toSheafPullbackComparison g).app M) :=
  (Category.comp_id _).symm.trans (unit_mateEquiv_symm (G := toSheaf X) (H := toSheaf Y)
    (Scheme.Modules.pullbackPushforwardAdjunction g)
    ((Opens.map g.base).sheafAdjunctionContinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)) (𝟙 _) M)

section Comp

variable {W Z : Scheme.{u}}

/-- The unit of `(a ≫ b)^* ⊣ (a ≫ b)_*` on underlying abelian sheaves, written through the units of
the inverse images along `b` and `a` and the comparisons `g⁻¹ ⟶ g^*` for `b` and `a`. -/
private lemma toSheaf_map_unit_comp (a : Z ⟶ W) (b : W ⟶ X) (M : X.Modules) :
    (toSheaf X).map ((Scheme.Modules.pullbackPushforwardAdjunction (a ≫ b)).unit.app M) =
      ((Opens.map b.base).sheafAdjunctionContinuous AddCommGrpCat.{u}
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology W)).unit.app
          ((toSheaf X).obj M) ≫
        ((Opens.map b.base).sheafPushforwardContinuous AddCommGrpCat.{u}
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology W)).map
          (((Opens.map a.base).sheafAdjunctionContinuous AddCommGrpCat.{u}
            (Opens.grothendieckTopology W) (Opens.grothendieckTopology Z)).unit.app
            (((Opens.map b.base).sheafPullback AddCommGrpCat.{u}
              (Opens.grothendieckTopology X) (Opens.grothendieckTopology W)).obj
              ((toSheaf X).obj M))) ≫
        ((Opens.map a.base).sheafPushforwardContinuous AddCommGrpCat.{u}
            (Opens.grothendieckTopology W) (Opens.grothendieckTopology Z) ⋙
          (Opens.map b.base).sheafPushforwardContinuous AddCommGrpCat.{u}
            (Opens.grothendieckTopology X) (Opens.grothendieckTopology W)).map
          (((Opens.map a.base).sheafPullback AddCommGrpCat.{u} (Opens.grothendieckTopology W)
            (Opens.grothendieckTopology Z)).map ((toSheafPullbackComparison b).app M) ≫
          (toSheafPullbackComparison a).app ((Scheme.Modules.pullback b).obj M) ≫
          (toSheaf Z).map ((Scheme.Modules.pullbackComp a b).hom.app M)) := by
  have hu : (pullbackPushforwardAdjunction (a ≫ b)).unit.app M =
      (pullbackPushforwardAdjunction b).unit.app M ≫
        (pushforward b).map ((pullbackPushforwardAdjunction a).unit.app ((pullback b).obj M)) ≫
        (pushforwardComp a b).hom.app _ ≫
          (pushforward (a ≫ b)).map ((pullbackComp a b).hom.app M) := by
    rw [← reassoc_of% unit_comp_pushforward_map_pullbackComp_inv_app a b M,
      ← Functor.map_comp, Iso.inv_hom_id_app]
    simp
  simp only [hu, Functor.map_comp]
  rw [reassoc_of% toSheafPullbackComparison_unit b M]
  refine (Category.assoc _ _ _).trans (congrArg
    (((Opens.map b.base).sheafAdjunctionContinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology W)).unit.app
        ((toSheaf X).obj M) ≫ ·) ?_)
  have nat := congrArg ((Opens.map b.base).sheafPushforwardContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology W)).map
    (((Opens.map a.base).sheafAdjunctionContinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology W) (Opens.grothendieckTopology Z)).unit.naturality
        ((toSheafPullbackComparison b).app M))
  simp only [Functor.comp_map, Functor.id_map, Functor.map_comp] at nat
  simp only [Functor.comp_map]
  rw [← reassoc_of% nat]
  refine congrArg (((Opens.map b.base).sheafPushforwardContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology W)).map
      ((toSheafPullbackComparison b).app M) ≫ ·) ?_
  -- The pushforward along `a ≫ b` is the composite of the pushforwards, definitionally.
  have e : (toSheaf X).map ((pushforward b).map
        ((pullbackPushforwardAdjunction a).unit.app ((pullback b).obj M)) ≫
        (pushforwardComp a b).hom.app _) =
      ((Opens.map b.base).sheafPushforwardContinuous AddCommGrpCat.{u}
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology W)).map
        ((toSheaf W).map ((pullbackPushforwardAdjunction a).unit.app ((pullback b).obj M))) :=
    congrArg (toSheaf X).map (Category.comp_id _)
  refine (congrArg (· ≫ _) e).trans ?_
  rw [toSheafPullbackComparison_unit a]
  -- `pushforwardComp a b` has identity components (`Scheme.Modules.pushforwardComp_hom_app_app`)
  -- between definitionally equal abelian sheaves, so its image under `toSheaf` is the identity.
  have h0 : (toSheaf X).map ((pushforwardComp a b).hom.app
      ((pullback a).obj ((pullback b).obj M))) = 𝟙 _ :=
    CategoryTheory.Functor.map_id _ _
  refine (congrArg (_ ≫ ·) ((congrArg (· ≫ _) h0).trans (Category.id_comp _))).trans ?_
  refine (congrArg (· ≫ _) (Functor.map_comp _ _ _)).trans ((Category.assoc _ _ _).trans ?_)
  refine congrArg (_ ≫ _ ≫ ·) ?_
  -- Over an open `U` of `X`, both sides are `(pullbackComp a b).hom.app M` over `a⁻¹ b⁻¹ U`, since
  -- the pushforward along `a ≫ b` and those along `a` then `b` evaluate at that open.
  ext U x
  rfl

/-- The comparison `g⁻¹ M ⟶ g^* M` for `a ≫ b`, after the isomorphism `a⁻¹ b⁻¹ ≅ (a ≫ b)⁻¹` of
inverse images of abelian sheaves, is the comparison for `b` followed by the comparison for `a`
and the isomorphism `a^* b^* M ≅ (a ≫ b)^* M`. -/
lemma toSheafPullbackComparison_comp (a : Z ⟶ W) (b : W ⟶ X) (M : X.Modules) :
    (Functor.sheafPullbackComp (Opens.map b.base) (Opens.map a.base) AddCommGrpCat.{u}
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology W)
        (Opens.grothendieckTopology Z)).hom.app ((toSheaf X).obj M) ≫
      (toSheafPullbackComparison (a ≫ b)).app M =
    ((Opens.map a.base).sheafPullback AddCommGrpCat.{u} (Opens.grothendieckTopology W)
        (Opens.grothendieckTopology Z)).map ((toSheafPullbackComparison b).app M) ≫
      (toSheafPullbackComparison a).app ((Scheme.Modules.pullback b).obj M) ≫
      (toSheaf Z).map ((Scheme.Modules.pullbackComp a b).hom.app M) := by
  let adj := ((Opens.map b.base).sheafAdjunctionContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology W)).comp
    ((Opens.map a.base).sheafAdjunctionContinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology W) (Opens.grothendieckTopology Z))
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.comp_unit_app]
  have hL := Functor.sheafAdjunctionContinuous_comp_unit_app (Opens.map b.base)
    (Opens.map a.base) AddCommGrpCat.{u} (Opens.grothendieckTopology X)
    (Opens.grothendieckTopology W) (Opens.grothendieckTopology Z) ((toSheaf X).obj M)
  have hab := toSheafPullbackComparison_unit (a ≫ b) M
  refine (?_ : _ = (toSheaf X).map
    ((Scheme.Modules.pullbackPushforwardAdjunction (a ≫ b)).unit.app M)).trans ?_
  · rw [hab]
    refine Eq.trans ?_ (congrArg (· ≫ _) hL.symm)
    simp only [Functor.map_comp, Category.assoc]
    -- The pushforward along `a ≫ b` of abelian sheaves, through the composite adjunction `adj`, is
    -- the pushforward along `a` and then `b` (`sheafPushforwardContinuousComp` is the identity).
    rfl
  · exact toSheaf_map_unit_comp a b M

end Comp

end AlgebraicGeometry.Scheme.Hom
