/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Basic
public import TauCeti.RepresentationTheory.OrbitSpace
import TauCeti.RepresentationTheory.Continuous.ContinuousRep.Basic
import TauCeti.Topology.Algebra.Module.ModuleTopology

/-!
# The coadjoint orbit space

The coadjoint orbit space `𝔤* / Ad* G` of a Lie group `G` is the quotient of the dual
`𝔤* = Module.Dual ℝ 𝔤` of the tangent Lie algebra `𝔤 = GroupLieAlgebra I G` by
`Representation.orbitRel` of the coadjoint representation `Ad*_g ν = ν ∘ Ad_{g⁻¹}`, with the
quotient topology. The dual carries no topology of its own; the results below hold for any topology
on `𝔤*` that is its module topology (`IsModuleTopology`), which for the finite-dimensional space
`𝔤*` is its unique Hausdorff vector-space topology. For it the coadjoint action is jointly
continuous, as the contragredient of the jointly continuous adjoint action (`ContinuousRep.dual`),
so the coadjoint orbit space of a compact Lie group is Hausdorff
(`Representation.t2Space_quotient_orbitRel`).

## Main results

* `TauCeti.Lie.continuous_coadjointRepresentation_apply`: the coadjoint action
  `(g, ν) ↦ Ad*_g ν` is jointly continuous.
* `TauCeti.Lie.t2Space_quotient_orbitRel_coadjointRepresentation`: the coadjoint orbit space of
  a compact Lie group is Hausdorff.
-/

public section

noncomputable section

namespace TauCeti.Lie

open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G]
  [TopologicalSpace (Module.Dual ℝ (GroupLieAlgebra I G))]
  [IsModuleTopology ℝ (Module.Dual ℝ (GroupLieAlgebra I G))]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- **The coadjoint action is jointly continuous.** For the module topology on the dual `𝔤*` of
the Lie algebra, the coadjoint action `(g, ν) ↦ Ad*_g ν = ν ∘ Ad_{g⁻¹}` of a finite-dimensional
real Lie group is jointly continuous. -/
theorem continuous_coadjointRepresentation_apply :
    Continuous fun p : G × Module.Dual ℝ (GroupLieAlgebra I G) ↦
      coadjointRepresentation ℝ I G p.1 p.2 := by
  have := topologicalGroup_of_lieGroup I ∞ (G := G)
  have : IsModuleTopology ℝ (GroupLieAlgebra I G) := isModuleTopologyOfFiniteDimensional
  -- The adjoint action on `𝔤` is jointly continuous, so its contragredient is too.
  have h := (ContinuousRep.mk (adjointRepresentation ℝ I G)
    continuous_adjointRepresentation_apply).dual.continuous_action
  rw [ContinuousRep.toRepresentation_dual] at h
  rwa [coadjointRepresentation_def]

/-- **The coadjoint orbit space of a compact Lie group is Hausdorff**, for the module topology on
the dual of the Lie algebra. -/
instance t2Space_quotient_orbitRel_coadjointRepresentation [CompactSpace G] :
    T2Space (Quotient (coadjointRepresentation ℝ I G).orbitRel) :=
  have := ModuleTopology.t2Space (Module.finBasis ℝ (Module.Dual ℝ (GroupLieAlgebra I G)))
  Representation.t2Space_quotient_orbitRel _ continuous_coadjointRepresentation_apply

end TauCeti.Lie
