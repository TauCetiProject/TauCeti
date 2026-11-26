/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Representation.Basic
public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Basic
public import TauCeti.RepresentationTheory.OrbitSpace
import TauCeti.Geometry.Lie.Adjoint.Smooth
import TauCeti.RepresentationTheory.Continuous.ContinuousRep.Basic
import TauCeti.Topology.Algebra.Module.ModuleTopology

/-!
# The adjoint and coadjoint orbit spaces

The adjoint orbit space `𝔤 / Ad G` of a Lie group `G` is the quotient of its Lie algebra by
`Representation.orbitRel` of the adjoint representation, with the quotient topology. This file
records that it is Hausdorff when `G` is compact, as the orbit space of a jointly continuous action
of a compact group on a Hausdorff space (`Representation.t2Space_quotient_orbitRel`).

The same holds for the coadjoint orbit space `𝔤* / Ad* G`, the quotient of the dual
`𝔤* = Module.Dual ℝ 𝔤` of the tangent Lie algebra `𝔤 = GroupLieAlgebra I G` by the coadjoint
representation `Ad*_g ν = ν ∘ Ad_{g⁻¹}`. The dual carries no topology of its own; the results
below hold for any topology on `𝔤*` that is its module topology (`IsModuleTopology`), which for the
finite-dimensional space `𝔤*` is its unique Hausdorff vector-space topology. For it the coadjoint
action is jointly continuous, as the contragredient of the jointly continuous adjoint action
(`ContinuousRep.dual`), so the coadjoint orbit space of a compact Lie group is Hausdorff as well.

## Main results

* `TauCeti.Lie.t2Space_quotient_orbitRel_continuousAdjointRepresentation`: the adjoint orbit
  space of a compact Lie group is Hausdorff.
* `TauCeti.Lie.continuous_coadjointRepresentation_apply`: the coadjoint action
  `(g, ν) ↦ Ad*_g ν` is jointly continuous.
* `TauCeti.Lie.t2Space_quotient_orbitRel_coadjointRepresentation`: the coadjoint orbit space of
  a compact Lie group is Hausdorff.
-/

public section

namespace TauCeti.Lie

open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

/-- **The adjoint orbit space of a compact Lie group is Hausdorff.** -/
instance t2Space_quotient_orbitRel_continuousAdjointRepresentation [T2Space G] [CompactSpace G] :
    T2Space
      (Quotient (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.orbitRel) :=
  Representation.t2Space_quotient_orbitRel _ continuous_continuousAdjointRepresentation_apply

section Coadjoint

variable [TopologicalSpace (Module.Dual ℝ (GroupLieAlgebra I G))]
  [IsModuleTopology ℝ (Module.Dual ℝ (GroupLieAlgebra I G))]

/-- **The coadjoint action is jointly continuous.** For the module topology on the dual `𝔤*` of
the Lie algebra, the coadjoint action `(g, ν) ↦ Ad*_g ν = ν ∘ Ad_{g⁻¹}` of a finite-dimensional
real Lie group is jointly continuous. -/
theorem continuous_coadjointRepresentation_apply :
    Continuous fun p : G × Module.Dual ℝ (GroupLieAlgebra I G) ↦
      coadjointRepresentation ℝ I G p.1 p.2 := by
  have := topologicalGroup_of_lieGroup I ∞ (G := G)
  have : IsModuleTopology ℝ (GroupLieAlgebra I G) := isModuleTopologyOfFiniteDimensional
  -- The adjoint action on `𝔤` is jointly continuous, so its contragredient is too.
  let ρ : ContinuousRep G ℝ (GroupLieAlgebra I G) :=
    { toRepresentation := adjointRepresentation ℝ I G
      continuous_action := by
        simp only [adjointRepresentation_apply]
        exact ((contMDiff_adjointContinuousLinearMap (I := I) (G := G)).continuous.comp
          continuous_fst).clm_apply continuous_snd }
  have h := ρ.dual.continuous_action
  rw [ContinuousRep.toRepresentation_dual] at h
  rwa [coadjointRepresentation_def]

/-- **The coadjoint orbit space of a compact Lie group is Hausdorff**, for the module topology on
the dual of the Lie algebra. -/
instance t2Space_quotient_orbitRel_coadjointRepresentation [CompactSpace G] :
    T2Space (Quotient (coadjointRepresentation ℝ I G).orbitRel) :=
  have := ModuleTopology.t2Space (Module.finBasis ℝ (Module.Dual ℝ (GroupLieAlgebra I G)))
  Representation.t2Space_quotient_orbitRel _ continuous_coadjointRepresentation_apply

end Coadjoint

end TauCeti.Lie
