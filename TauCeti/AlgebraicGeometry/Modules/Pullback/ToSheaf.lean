/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Adjunction.Mates
public import TauCeti.AlgebraicGeometry.Modules.Sheaf
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
  is the unit of the abelian inverse image followed by the comparison.
-/

public section

open CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry.Scheme.Modules

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

end AlgebraicGeometry.Scheme.Hom
