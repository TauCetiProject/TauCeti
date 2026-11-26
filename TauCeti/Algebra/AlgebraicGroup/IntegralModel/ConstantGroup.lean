/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ConstantGroup.SchemeProperties
public import TauCeti.Algebra.AlgebraicGroup.IntegralModel.Basic

/-!
# Models of constant groups do not have connected fibers

`SmoothModel.HasConnectedFibers` tests both selected fibers of a model, the generic one first. A
nontrivial finite constant group over a field `K` is disconnected, so no smooth `O`-model of it,
over any local ring `O`, has connected fibers, whatever its special fiber is.

## Main declarations

* `TauCeti.IntegralModel.SmoothModel.not_hasConnectedFibers_constantGroup`: a model of a
  nontrivial finite constant group does not have connected fibers.
-/

public section

namespace TauCeti.IntegralModel.SmoothModel

universe u

variable (G : Type u) [Group G] [Finite G] (K : Type u) [Field K]

/-- **A model of a nontrivial finite constant group does not have connected fibers**: its generic
fiber is the constant group, which is disconnected. -/
theorem not_hasConnectedFibers_constantGroup [Nontrivial G] {O : Type u} [CommRing O]
    [IsLocalRing O] [Algebra O K]
    (𝒢 : SmoothModel O K (ConstantGroup.finiteTypeCoordinateHopfAlgebra K G)) :
    ¬ 𝒢.HasConnectedFibers := fun h ↦
  ConstantGroup.not_geometricallyConnected_finiteTypeCoordinateHopfAlgebra G K h.genericFiber

end TauCeti.IntegralModel.SmoothModel
