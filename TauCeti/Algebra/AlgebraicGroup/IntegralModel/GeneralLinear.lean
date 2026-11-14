/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Coordinate.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Reductive.Over
public import TauCeti.Algebra.AlgebraicGroup.IntegralModel.Basic

/-!
# The standard integral model of `GL_n`

For a commutative ring `O` with an algebra map to a field `K`, the general linear group scheme
`GL_{n,O}` is a smooth affine `O`-model of `GL_{n,K}`
(`TauCeti.IntegralModel.SmoothModel.generalLinear`). When `O` is local it is a reductive model,
so its integral points form a hyperspecial subgroup of the `K`-points of `GL_n`.

## Main declarations

* `TauCeti.IntegralModel.SmoothModel.generalLinear`: the standard model of `GL_n`.
* `TauCeti.IntegralModel.SmoothModel.isReductive_generalLinear`: it is reductive over a local
  ring.
* `TauCeti.IntegralModel.SmoothModel.isHyperspecialSubgroup_generalLinear`: its integral points
  form a hyperspecial subgroup.
-/

public section

namespace TauCeti.IntegralModel.SmoothModel

universe u

variable (O K : Type u) [CommRing O] [Field K] [Algebra O K]

/-- The standard smooth model `GL_{n,O}` of `GL_{n,K}`. -/
@[expose] noncomputable def generalLinear (n : ℕ) :
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
coordinate algebra of `GL_n`. -/
@[simp]
theorem generalLinear_genericFiberIso (n : ℕ) :
    (generalLinear O K n).genericFiberIso =
      GeneralLinear.finiteTypeCoordinateHopfAlgebraBaseChangeIso O K n :=
  (rfl)

variable [IsLocalRing O]

/-- The standard model `GL_{n,O}` is a reductive model of `GL_{n,K}`. -/
theorem isReductive_generalLinear (n : ℕ) : (generalLinear O K n).IsReductive :=
  isReductive_of_reductiveCommHopfAlgPropertyOver
    (GeneralLinear.reductiveCommHopfAlgPropertyOver_finiteTypeCoordinateHopfAlgebra O n)

/-- Both fibers `GL_{n,K}` and `GL_{n,κ}` of the standard model are geometrically connected. -/
theorem hasConnectedFibers_generalLinear (n : ℕ) : (generalLinear O K n).HasConnectedFibers :=
  (isReductive_generalLinear O K n).hasConnectedFibers

/-- The integral points of the standard model `GL_{n,O}` form a hyperspecial subgroup of the
`K`-points of `GL_n`. -/
theorem isHyperspecialSubgroup_generalLinear (n : ℕ) :
    IsHyperspecialSubgroup O (generalLinear O K n).integralPoints :=
  (isReductive_generalLinear O K n).isHyperspecialSubgroup

end TauCeti.IntegralModel.SmoothModel
