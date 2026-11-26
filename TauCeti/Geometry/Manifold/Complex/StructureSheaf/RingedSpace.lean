/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.LocalRing
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace

/-!
# The holomorphic locally ringed space of a complex manifold

A charted space on a complex model with corners, equipped with its sheaf of holomorphic
functions `TauCeti.holomorphicStructureSheaf`, is a sheafed space of commutative rings
(`TauCeti.holomorphicStructureSheaf.sheafedSpace`). Its stalks are local rings
(`TauCeti.holomorphicStructureSheaf.instIsLocalRingStalk`), so it is a locally ringed space
(`TauCeti.holomorphicStructureSheaf.locallyRingedSpace`).

For a boundaryless finite-dimensional model, `TauCeti.holomorphicStructureSheaf.smoothSheafIso`
identifies this sheaf with the structure sheaf of Mathlib's `ChartedSpace.locallyRingedSpace`.
The present definitions need no such hypothesis on the model. They are the ringed spaces of
normalizations of nodal curves, whose glued structure sheaves are subsheaves of direct images of
holomorphic structure sheaves.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.holomorphicStructureSheaf

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (X : Type) [TopologicalSpace X] [ChartedSpace H X]

/-- A complex charted space with its sheaf of holomorphic functions. -/
abbrev sheafedSpace : SheafedSpace CommRingCat where
  carrier := TopCat.of X
  presheaf := (holomorphicStructureSheaf I X).presheaf
  IsSheaf := (holomorphicStructureSheaf I X).property

/-- A complex charted space with its sheaf of holomorphic functions, whose stalks are local
rings. -/
abbrev locallyRingedSpace : LocallyRingedSpace where
  toSheafedSpace := sheafedSpace I X
  isLocalRing := instIsLocalRingStalk I X

end TauCeti.holomorphicStructureSheaf
