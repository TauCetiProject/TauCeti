/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Reductive.Over
public import TauCeti.Algebra.AlgebraicGroup.IntegralModel.Reductive

/-!
# The standard integral model of `GL_n`

For a commutative ring `O` with an algebra map to a commutative ring `K`, the general linear
group scheme `GL_{n,O}` is a smooth affine `O`-model of `GL_{n,K}`
(`TauCeti.IntegralModel.SmoothModel.generalLinear`). When `O` is local and `K` is a field it is a
reductive model, so its integral points satisfy `TauCeti.IntegralModel.IsHyperspecialSubgroup`.

## Main declarations

* `TauCeti.IntegralModel.SmoothModel.generalLinear`: the standard model of `GL_n`.
* `TauCeti.IntegralModel.SmoothModel.isReductive_generalLinear`: it is reductive over a local
  ring with a field `K`.
* `TauCeti.IntegralModel.SmoothModel.isHyperspecialSubgroup_generalLinear`: its integral points
  satisfy `IsHyperspecialSubgroup`.
-/

public section

open CategoryTheory

namespace TauCeti.IntegralModel.SmoothModel

universe u

section CommRing

variable (O K : Type u) [CommRing O] [CommRing K] [Algebra O K]

/-- The standard smooth model `GL_{n,O}` of `GL_{n,K}`. -/
noncomputable def generalLinear (n : ℕ) :
    SmoothModel O K (GeneralLinear.finiteTypeCoordinateHopfAlgebra K n) where
  coord := GeneralLinear.finiteTypeCoordinateHopfAlgebra O n
  smooth := (GeneralLinear.reductiveCommHopfAlgPropertyOver_finiteTypeCoordinateHopfAlgebra
    O n).smooth
  genericFiberIso := GeneralLinear.finiteTypeCoordinateHopfAlgebraBaseChangeIso O K n

/-- The coordinate algebra of the standard model is the coordinate algebra of `GL_{n,O}`. -/
@[simp]
theorem generalLinear_coord (n : ℕ) :
    (generalLinear O K n).coord = GeneralLinear.finiteTypeCoordinateHopfAlgebra O n :=
  (rfl)

/-- The generic fiber isomorphism of the standard model is the base change isomorphism of the
coordinate algebra of `GL_n`, transported along `generalLinear_coord`. -/
@[simp]
theorem generalLinear_genericFiberIso (n : ℕ) :
    (generalLinear O K n).genericFiberIso =
      eqToIso (congrArg (FiniteTypeCommHopfAlgCat.baseChange (K := K))
        (generalLinear_coord O K n)) ≪≫
        GeneralLinear.finiteTypeCoordinateHopfAlgebraBaseChangeIso O K n := by
  -- `generalLinear_coord` holds by `rfl`, so the transport `eqToHom` is the identity.
  ext1
  exact (Category.id_comp _).symm

end CommRing

variable (O K : Type u) [CommRing O] [IsLocalRing O] [Field K] [Algebra O K]

/-- The standard model `GL_{n,O}` is a reductive model of `GL_{n,K}`. -/
theorem isReductive_generalLinear (n : ℕ) : (generalLinear O K n).IsReductive :=
  isReductive_of_reductiveCommHopfAlgPropertyOver
    (GeneralLinear.reductiveCommHopfAlgPropertyOver_finiteTypeCoordinateHopfAlgebra O n)

/-- The two selected base changes `GL_{n,K}` and `GL_{n,κ}` of the standard model are
geometrically connected. -/
theorem hasConnectedFibers_generalLinear (n : ℕ) : (generalLinear O K n).HasConnectedFibers :=
  (isReductive_generalLinear O K n).hasConnectedFibers

/-- The integral points of the standard model `GL_{n,O}` satisfy `IsHyperspecialSubgroup O`. -/
theorem isHyperspecialSubgroup_generalLinear (n : ℕ) :
    IsHyperspecialSubgroup O (generalLinear O K n).integralPoints :=
  (isReductive_generalLinear O K n).isHyperspecialSubgroup

end TauCeti.IntegralModel.SmoothModel
