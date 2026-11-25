/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Representation.Basic
public import TauCeti.RepresentationTheory.OrbitSpace

/-!
# The adjoint orbit space

The adjoint orbit space `𝔤 / Ad G` of a Lie group `G` is the quotient of its Lie algebra by
`Representation.orbitRel` of the adjoint representation, with the quotient topology. This file
records that it is Hausdorff when `G` is compact, as the orbit space of a jointly continuous action
of a compact group on a Hausdorff space (`Representation.t2Space_quotient_orbitRel`).

## Main results

* `TauCeti.Lie.t2Space_quotient_orbitRel_continuousAdjointRepresentation`: the adjoint orbit
  space of a compact Lie group is Hausdorff.
-/

public section

namespace TauCeti.Lie

open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G] [CompactSpace G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

/-- **The adjoint orbit space of a compact Lie group is Hausdorff.** -/
instance t2Space_quotient_orbitRel_continuousAdjointRepresentation :
    T2Space
      (Quotient (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.orbitRel) :=
  Representation.t2Space_quotient_orbitRel _ continuous_continuousAdjointRepresentation_apply

end TauCeti.Lie
