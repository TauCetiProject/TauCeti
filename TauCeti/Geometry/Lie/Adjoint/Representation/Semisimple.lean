/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Semisimple
public import TauCeti.Geometry.Lie.Adjoint.Representation.Basic

import TauCeti.RepresentationTheory.Compact.Semisimple

/-!
# Semisimplicity of the adjoint representation of a compact subgroup

The adjoint action of a compact subgroup `K` of a smooth real Lie group `G` with finite-dimensional
model on the tangent Lie algebra `𝔤 = GroupLieAlgebra I G` is continuous, hence completely
reducible.

## Main results

* `TauCeti.Lie.isSemisimpleRepresentation_adjointRepresentation_comp_subtype`: the adjoint
  representation of a compact subgroup is semisimple.
-/

public section

noncomputable section

namespace TauCeti.Lie

open scoped Manifold ContDiff

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]

/-- **The adjoint representation of a compact subgroup is semisimple.** The adjoint action of a
compact subgroup `K` of a smooth real Lie group with finite-dimensional model is continuous, hence
completely reducible (`Representation.isSemisimpleRepresentation_of_continuous`). -/
theorem isSemisimpleRepresentation_adjointRepresentation_comp_subtype {K : Subgroup G}
    (hK : IsCompact (K : Set G)) :
    Representation.IsSemisimpleRepresentation ((adjointRepresentation ℝ I G).comp K.subtype) := by
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  refine Representation.isSemisimpleRepresentation_of_continuous _ fun f ξ ↦ ?_
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, adjointRepresentation_apply]
  exact (LinearMap.continuous_of_finiteDimensional f).comp
    (((contMDiff_adjointContinuousLinearMap (I := I) (G := G)).continuous.comp
      continuous_subtypeVal).clm_apply continuous_const)

end TauCeti.Lie
