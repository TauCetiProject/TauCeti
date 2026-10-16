/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Immersed.Basic
public import TauCeti.Geometry.Lie.Subgroup.Differential

/-!
# The differential of an immersed Lie subgroup presentation

An immersed Lie subgroup is presented by a connected Lie group `X` and an injective smooth
immersion `X → G` whose image is the specified subgroup `K`. The Lie functor sends this
presentation to an injective Lie-algebra homomorphism. Naturality of the exponential shows that
its range lies in the ambient Lie algebra associated to `K`: every one-parameter subgroup in the
image comes from a one-parameter subgroup of `X`, hence remains in `K`.

The source has its intrinsic manifold topology, which need not be the subspace topology inherited
from `G`. None of the arguments below identify those topologies. The source Lie-group structure
supplies the Hausdorff instance needed by the exponential API.

## Main results

* `TauCeti.Lie.ImmersedLieSubgroupData.toContMDiffMonoidMorphism`: the presenting homomorphism as
  a smooth monoid morphism.
* `TauCeti.Lie.ImmersedLieSubgroupData.lieMapToHom`: its differential at the identity.
* `TauCeti.Lie.ImmersedLieSubgroupData.injective_lieMapToHom`: the differential is injective.
* `TauCeti.Lie.ImmersedLieSubgroupData.range_lieMapToHom_le`: its range lies in
  `TauCeti.Lie.lieSubalgebraOfSubgroup K`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd edition (2013), Chapters 8 and 20.
-/

public section

noncomputable section

open scoped ContDiff Manifold

universe u v w

namespace TauCeti.Lie.ImmersedLieSubgroupData

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type w} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {K : Subgroup G} [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G]

attribute [local instance] ContMDiffMul.boundarylessManifold
attribute [local instance] LieGroup.minSmoothnessThree

/-- The homomorphism presenting an immersed Lie subgroup, packaged as a smooth monoid morphism. -/
def toContMDiffMonoidMorphism (d : ImmersedLieSubgroupData I K) :
    let _ : Group d.X := d.group
    let _ : TopologicalSpace d.X := d.topologicalSpace
    let _ : NormedAddCommGroup d.E' := d.normedAddCommGroup
    let _ : NormedSpace ℝ d.E' := d.normedSpace
    let _ : FiniteDimensional ℝ d.E' := d.finiteDimensional
    let _ : TopologicalSpace d.H' := d.modelTopology
    let _ : ChartedSpace d.H' d.X := d.chartedSpace
    let _ : IsManifold d.I' ∞ d.X := d.isManifold
    let _ : LieGroup d.I' ∞ d.X := d.lieGroup
    ContMDiffMonoidMorphism d.I' I ∞ d.X G := by
  let _ : Group d.X := d.group
  let _ : TopologicalSpace d.X := d.topologicalSpace
  let _ : NormedAddCommGroup d.E' := d.normedAddCommGroup
  let _ : NormedSpace ℝ d.E' := d.normedSpace
  let _ : FiniteDimensional ℝ d.E' := d.finiteDimensional
  let _ : TopologicalSpace d.H' := d.modelTopology
  let _ : ChartedSpace d.H' d.X := d.chartedSpace
  let _ : IsManifold d.I' ∞ d.X := d.isManifold
  let _ : LieGroup d.I' ∞ d.X := d.lieGroup
  exact { toMonoidHom := d.toHom, contMDiff_toFun := d.contMDiff_toHom }

omit [FiniteDimensional ℝ E] [T2Space G] in
/-- The smooth monoid morphism underlying an immersed presentation is its presenting
homomorphism. -/
@[simp]
theorem toContMDiffMonoidMorphism_apply (d : ImmersedLieSubgroupData I K) :
    let _ : Group d.X := d.group
    let _ : TopologicalSpace d.X := d.topologicalSpace
    let _ : NormedAddCommGroup d.E' := d.normedAddCommGroup
    let _ : NormedSpace ℝ d.E' := d.normedSpace
    let _ : FiniteDimensional ℝ d.E' := d.finiteDimensional
    let _ : TopologicalSpace d.H' := d.modelTopology
    let _ : ChartedSpace d.H' d.X := d.chartedSpace
    let _ : IsManifold d.I' ∞ d.X := d.isManifold
    let _ : LieGroup d.I' ∞ d.X := d.lieGroup
    ∀ x : d.X, d.toContMDiffMonoidMorphism x = d.toHom x := by
  let _ : Group d.X := d.group
  let _ : TopologicalSpace d.X := d.topologicalSpace
  let _ : NormedAddCommGroup d.E' := d.normedAddCommGroup
  let _ : NormedSpace ℝ d.E' := d.normedSpace
  let _ : FiniteDimensional ℝ d.E' := d.finiteDimensional
  let _ : TopologicalSpace d.H' := d.modelTopology
  let _ : ChartedSpace d.H' d.X := d.chartedSpace
  let _ : IsManifold d.I' ∞ d.X := d.isManifold
  let _ : LieGroup d.I' ∞ d.X := d.lieGroup
  dsimp only
  intro x
  rfl

/-- The Lie map induced by the homomorphism presenting an immersed Lie subgroup. -/
noncomputable def lieMapToHom (d : ImmersedLieSubgroupData I K) :
    let _ : Group d.X := d.group
    let _ : TopologicalSpace d.X := d.topologicalSpace
    let _ : NormedAddCommGroup d.E' := d.normedAddCommGroup
    let _ : NormedSpace ℝ d.E' := d.normedSpace
    let _ : FiniteDimensional ℝ d.E' := d.finiteDimensional
    let _ : TopologicalSpace d.H' := d.modelTopology
    let _ : ChartedSpace d.H' d.X := d.chartedSpace
    let _ : IsManifold d.I' ∞ d.X := d.isManifold
    let _ : LieGroup d.I' ∞ d.X := d.lieGroup
    LeftInvariantDerivation d.I' d.X →ₗ⁅ℝ⁆ LeftInvariantDerivation I G := by
  let _ : Group d.X := d.group
  let _ : TopologicalSpace d.X := d.topologicalSpace
  let _ : NormedAddCommGroup d.E' := d.normedAddCommGroup
  let _ : NormedSpace ℝ d.E' := d.normedSpace
  let _ : FiniteDimensional ℝ d.E' := d.finiteDimensional
  let _ : TopologicalSpace d.H' := d.modelTopology
  let _ : ChartedSpace d.H' d.X := d.chartedSpace
  let _ : IsManifold d.I' ∞ d.X := d.isManifold
  let _ : LieGroup d.I' ∞ d.X := d.lieGroup
  exact lieMap d.toContMDiffMonoidMorphism

omit [T2Space G] in
/-- The immersed-presentation Lie map is the Lie functor applied to its smooth homomorphism. -/
@[simp]
theorem lieMapToHom_apply (d : ImmersedLieSubgroupData I K) :
    let _ : Group d.X := d.group
    let _ : TopologicalSpace d.X := d.topologicalSpace
    let _ : NormedAddCommGroup d.E' := d.normedAddCommGroup
    let _ : NormedSpace ℝ d.E' := d.normedSpace
    let _ : FiniteDimensional ℝ d.E' := d.finiteDimensional
    let _ : TopologicalSpace d.H' := d.modelTopology
    let _ : ChartedSpace d.H' d.X := d.chartedSpace
    let _ : IsManifold d.I' ∞ d.X := d.isManifold
    let _ : LieGroup d.I' ∞ d.X := d.lieGroup
    ∀ X : LeftInvariantDerivation d.I' d.X,
      d.lieMapToHom X = lieMap d.toContMDiffMonoidMorphism X := by
  let _ : Group d.X := d.group
  let _ : TopologicalSpace d.X := d.topologicalSpace
  let _ : NormedAddCommGroup d.E' := d.normedAddCommGroup
  let _ : NormedSpace ℝ d.E' := d.normedSpace
  let _ : FiniteDimensional ℝ d.E' := d.finiteDimensional
  let _ : TopologicalSpace d.H' := d.modelTopology
  let _ : ChartedSpace d.H' d.X := d.chartedSpace
  let _ : IsManifold d.I' ∞ d.X := d.isManifold
  let _ : LieGroup d.I' ∞ d.X := d.lieGroup
  dsimp only
  intro X
  rfl

omit [T2Space G] in
/-- The Lie map induced by an immersed subgroup presentation is injective. -/
theorem injective_lieMapToHom (d : ImmersedLieSubgroupData I K) :
    let _ : Group d.X := d.group
    let _ : TopologicalSpace d.X := d.topologicalSpace
    let _ : NormedAddCommGroup d.E' := d.normedAddCommGroup
    let _ : NormedSpace ℝ d.E' := d.normedSpace
    let _ : FiniteDimensional ℝ d.E' := d.finiteDimensional
    let _ : TopologicalSpace d.H' := d.modelTopology
    let _ : ChartedSpace d.H' d.X := d.chartedSpace
    let _ : IsManifold d.I' ∞ d.X := d.isManifold
    let _ : LieGroup d.I' ∞ d.X := d.lieGroup
    Function.Injective d.lieMapToHom := by
  let _ : Group d.X := d.group
  let _ : TopologicalSpace d.X := d.topologicalSpace
  let _ : NormedAddCommGroup d.E' := d.normedAddCommGroup
  let _ : NormedSpace ℝ d.E' := d.normedSpace
  let _ : FiniteDimensional ℝ d.E' := d.finiteDimensional
  let _ : TopologicalSpace d.H' := d.modelTopology
  let _ : ChartedSpace d.H' d.X := d.chartedSpace
  let _ : IsManifold d.I' ∞ d.X := d.isManifold
  let _ : LieGroup d.I' ∞ d.X := d.lieGroup
  dsimp only
  apply lieMap_injective_of_mfderiv_injective
  exact d.injective_mfderiv_toHom 1

/-- The differential of an immersed presentation takes every source derivation into the ambient
Lie subalgebra associated to its image subgroup. -/
theorem lieMapToHom_mem_lieSubalgebraOfSubgroup (d : ImmersedLieSubgroupData I K) :
    let _ : Group d.X := d.group
    let _ : TopologicalSpace d.X := d.topologicalSpace
    let _ : NormedAddCommGroup d.E' := d.normedAddCommGroup
    let _ : NormedSpace ℝ d.E' := d.normedSpace
    let _ : FiniteDimensional ℝ d.E' := d.finiteDimensional
    let _ : TopologicalSpace d.H' := d.modelTopology
    let _ : ChartedSpace d.H' d.X := d.chartedSpace
    let _ : IsManifold d.I' ∞ d.X := d.isManifold
    let _ : LieGroup d.I' ∞ d.X := d.lieGroup
    ∀ X : LeftInvariantDerivation d.I' d.X,
      d.lieMapToHom X ∈ lieSubalgebraOfSubgroup (I := I) K := by
  let _ : Group d.X := d.group
  let _ : TopologicalSpace d.X := d.topologicalSpace
  let _ : NormedAddCommGroup d.E' := d.normedAddCommGroup
  let _ : NormedSpace ℝ d.E' := d.normedSpace
  let _ : FiniteDimensional ℝ d.E' := d.finiteDimensional
  let _ : TopologicalSpace d.H' := d.modelTopology
  let _ : ChartedSpace d.H' d.X := d.chartedSpace
  let _ : IsManifold d.I' ∞ d.X := d.isManifold
  let _ : LieGroup d.I' ∞ d.X := d.lieGroup
  dsimp only
  intro X
  apply range_lieMap_le_lieSubalgebraOfSubgroup d.toContMDiffMonoidMorphism
  · simpa only [toContMDiffMonoidMorphism] using le_of_eq d.range_eq
  · exact ⟨X, rfl⟩

/-- The range of the differential of an immersed presentation lies in the ambient Lie subalgebra
associated to its image subgroup. -/
theorem range_lieMapToHom_le (d : ImmersedLieSubgroupData I K) :
    let _ : Group d.X := d.group
    let _ : TopologicalSpace d.X := d.topologicalSpace
    let _ : NormedAddCommGroup d.E' := d.normedAddCommGroup
    let _ : NormedSpace ℝ d.E' := d.normedSpace
    let _ : FiniteDimensional ℝ d.E' := d.finiteDimensional
    let _ : TopologicalSpace d.H' := d.modelTopology
    let _ : ChartedSpace d.H' d.X := d.chartedSpace
    let _ : IsManifold d.I' ∞ d.X := d.isManifold
    let _ : LieGroup d.I' ∞ d.X := d.lieGroup
    d.lieMapToHom.range ≤ lieSubalgebraOfSubgroup (I := I) K := by
  let _ : Group d.X := d.group
  let _ : TopologicalSpace d.X := d.topologicalSpace
  let _ : NormedAddCommGroup d.E' := d.normedAddCommGroup
  let _ : NormedSpace ℝ d.E' := d.normedSpace
  let _ : FiniteDimensional ℝ d.E' := d.finiteDimensional
  let _ : TopologicalSpace d.H' := d.modelTopology
  let _ : ChartedSpace d.H' d.X := d.chartedSpace
  let _ : IsManifold d.I' ∞ d.X := d.isManifold
  let _ : LieGroup d.I' ∞ d.X := d.lieGroup
  dsimp only
  apply range_lieMap_le_lieSubalgebraOfSubgroup d.toContMDiffMonoidMorphism
  simpa only [toContMDiffMonoidMorphism] using le_of_eq d.range_eq

end TauCeti.Lie.ImmersedLieSubgroupData
