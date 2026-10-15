/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.Immersion

/-!
# Immersed Lie subgroups

An immersed Lie subgroup of a Lie group `G` need not use the topology inherited from `G`.  For
example, a dense one-parameter subgroup of a torus has its natural one-dimensional manifold
topology, which is finer than its subspace topology.  Consequently, an immersed subgroup is
represented here by a connected Lie group `X` together with an injective smooth immersion into
`G`, rather than by putting manifold instances on the subtype of a `Subgroup G`.

`TauCeti.Lie.ImmersedLieSubgroupData I K` records such a presentation whose image is exactly `K`.
The existential predicate `TauCeti.Lie.IsImmersedLieSubgroup I K` forgets the choice of source and
its manifold structure.  Mathlib's `Manifold.IsImmersion` is used directly, so smoothness and
injectivity of the differential are consequences rather than duplicated fields.

This is the carrier interface for constructing connected immersed subgroups from integral leaves
of left-invariant distributions.

## Main definitions and results

* `TauCeti.Lie.ImmersedLieSubgroupData`: a connected Lie group mapping injectively and immersively
  onto a specified subgroup, with a finite-dimensional source model.
* `TauCeti.Lie.IsImmersedLieSubgroup`: existence of immersed-Lie-subgroup data.
* `TauCeti.Lie.ImmersedLieSubgroupData.contMDiff_toHom`: the presenting homomorphism is smooth.
* `TauCeti.Lie.ImmersedLieSubgroupData.injective_mfderiv_toHom`: its differential is injective.
* `TauCeti.Lie.isImmersedLieSubgroup_top`: a connected Lie group is an immersed subgroup of itself.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd edition (2013), Chapter 19.
-/

public section

noncomputable section

open scoped ContDiff Manifold

universe u v w

namespace TauCeti.Lie

/-- Data presenting a subgroup `K` of a Lie group modeled on `I` as a connected immersed Lie
subgroup.

The source `X` carries its own topology and smooth structure.  The homomorphism `toHom` is
injective, has range exactly `K`, and is an immersion.  Thus the topology of `X` is not required
to agree with the subspace topology on `K`; this is the distinction between immersed and embedded
Lie subgroups. -/
structure ImmersedLieSubgroupData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {G : Type w} [TopologicalSpace G] [ChartedSpace H G] [Group G]
    [LieGroup I ∞ G]
    (K : Subgroup G) where
  /-- The smooth manifold structure on the ambient group. -/
  [ambientIsManifold : IsManifold I ∞ G]
  /-- The connected Lie group which parametrizes the immersed subgroup. -/
  X : Type w
  /-- The group structure on the source. -/
  [group : Group X]
  /-- The intrinsic topology on the source. -/
  [topologicalSpace : TopologicalSpace X]
  /-- The model vector space of the source. -/
  E' : Type u
  /-- The additive topological structure on the source model space. -/
  [normedAddCommGroup : NormedAddCommGroup E']
  /-- The real normed-space structure on the source model space. -/
  [normedSpace : NormedSpace ℝ E']
  /-- The source model space is finite-dimensional. -/
  [finiteDimensional : FiniteDimensional ℝ E']
  /-- The model chart target of the source. -/
  H' : Type v
  /-- The topology on the source model chart target. -/
  [modelTopology : TopologicalSpace H']
  /-- The model with corners for the source. -/
  I' : ModelWithCorners ℝ E' H'
  /-- The charted-space structure on the source. -/
  [chartedSpace : ChartedSpace H' X]
  /-- The smooth manifold structure on the source. -/
  [isManifold : IsManifold I' ∞ X]
  /-- The smooth Lie-group structure on the source. -/
  [lieGroup : LieGroup I' ∞ X]
  /-- The source is connected. -/
  [connectedSpace : ConnectedSpace X]
  /-- The homomorphism from the source to the ambient Lie group. -/
  toHom : X →* G
  /-- The presenting homomorphism is injective. -/
  injective : Function.Injective toHom
  /-- The image of the presenting homomorphism is exactly the specified subgroup. -/
  range_eq : MonoidHom.range toHom = K
  /-- The presenting homomorphism is a smooth immersion. -/
  isImmersion : Manifold.IsImmersion I' I ∞ (toHom : X → G)

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type w} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]

namespace ImmersedLieSubgroupData

variable {K : Subgroup G}

/-- The homomorphism presenting an immersed Lie subgroup is smooth. -/
theorem contMDiff_toHom (d : ImmersedLieSubgroupData I K) :
    let _ : Group d.X := d.group
    let _ : TopologicalSpace d.X := d.topologicalSpace
    let _ : NormedAddCommGroup d.E' := d.normedAddCommGroup
    let _ : NormedSpace ℝ d.E' := d.normedSpace
    let _ : TopologicalSpace d.H' := d.modelTopology
    let _ : ChartedSpace d.H' d.X := d.chartedSpace
    let _ : IsManifold d.I' ∞ d.X := d.isManifold
    let _ : LieGroup d.I' ∞ d.X := d.lieGroup
    ContMDiff d.I' I ∞ (d.toHom : d.X → G) := by
  dsimp only
  let _ : Group d.X := d.group
  let _ : TopologicalSpace d.X := d.topologicalSpace
  let _ : NormedAddCommGroup d.E' := d.normedAddCommGroup
  let _ : NormedSpace ℝ d.E' := d.normedSpace
  let _ : TopologicalSpace d.H' := d.modelTopology
  let _ : ChartedSpace d.H' d.X := d.chartedSpace
  let _ : IsManifold d.I' ∞ d.X := d.isManifold
  let _ : LieGroup d.I' ∞ d.X := d.lieGroup
  exact d.isImmersion.contMDiff

/-- The differential of the homomorphism presenting an immersed Lie subgroup is injective at
every point. -/
theorem injective_mfderiv_toHom (d : ImmersedLieSubgroupData I K) (x : d.X) :
    let _ : Group d.X := d.group
    let _ : TopologicalSpace d.X := d.topologicalSpace
    let _ : NormedAddCommGroup d.E' := d.normedAddCommGroup
    let _ : NormedSpace ℝ d.E' := d.normedSpace
    let _ : TopologicalSpace d.H' := d.modelTopology
    let _ : ChartedSpace d.H' d.X := d.chartedSpace
    let _ : IsManifold d.I' ∞ d.X := d.isManifold
    let _ : LieGroup d.I' ∞ d.X := d.lieGroup
    Function.Injective (mfderiv d.I' I (d.toHom : d.X → G) x) := by
  dsimp only
  let _ : Group d.X := d.group
  let _ : TopologicalSpace d.X := d.topologicalSpace
  let _ : NormedAddCommGroup d.E' := d.normedAddCommGroup
  let _ : NormedSpace ℝ d.E' := d.normedSpace
  let _ : TopologicalSpace d.H' := d.modelTopology
  let _ : ChartedSpace d.H' d.X := d.chartedSpace
  let _ : IsManifold d.I' ∞ d.X := d.isManifold
  let _ : LieGroup d.I' ∞ d.X := d.lieGroup
  exact d.isImmersion.mfderiv_injective (by simp) x

end ImmersedLieSubgroupData

/-- A subgroup is an immersed Lie subgroup when it is the image of an injective smooth immersion
from a connected Lie group carrying its own manifold topology. -/
def IsImmersedLieSubgroup (K : Subgroup G) : Prop :=
  Nonempty (ImmersedLieSubgroupData I K)

/-- Characterization of `TauCeti.Lie.IsImmersedLieSubgroup` by the data it forgets. -/
@[simp]
theorem isImmersedLieSubgroup_iff {K : Subgroup G} :
    IsImmersedLieSubgroup (I := I) K ↔ Nonempty (ImmersedLieSubgroupData I K) :=
  Iff.rfl

/-- Immersed-Lie-subgroup data exhibits its specified subgroup as an immersed Lie subgroup. -/
theorem ImmersedLieSubgroupData.isImmersedLieSubgroup {K : Subgroup G}
    (d : ImmersedLieSubgroupData I K) : IsImmersedLieSubgroup (I := I) K :=
  ⟨d⟩

/-- A connected Lie group is an immersed Lie subgroup of itself via the identity homomorphism. -/
@[simp 1100]
theorem isImmersedLieSubgroup_top [FiniteDimensional ℝ E] [ConnectedSpace G] :
    IsImmersedLieSubgroup (I := I) (⊤ : Subgroup G) := by
  exact ⟨{
    ambientIsManifold := IsManifold.mk' I ∞ G
    X := G
    E' := E
    H' := H
    I' := I
    isManifold := IsManifold.mk' I ∞ G
    toHom := MonoidHom.id G
    injective := Function.injective_id
    range_eq := MonoidHom.range_eq_top.mpr Function.surjective_id
    isImmersion := Manifold.IsImmersion.id
  }⟩

end TauCeti.Lie
