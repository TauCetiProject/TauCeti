/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Atlas
public import TauCeti.Geometry.Lie.Subgroup.Immersion

/-!
# Embedded Lie subgroups and the closed-subgroup theorem

A subgroup `K` of a Lie group `G` is an *embedded Lie subgroup* when it carries a smooth structure,
for its subspace topology, making it a Lie group whose inclusion into `G` is smooth and an
immersion.  `TauCeti.Lie.EmbeddedLieSubgroupData` is that structure together with a choice of model
vector space, and `TauCeti.Lie.IsEmbeddedLieSubgroup` is its existential form.  Because the
underlying topological space of `K` is the subspace topology of `G`, the inclusion is automatically
a topological embedding, which is what distinguishes an embedded from a merely immersed subgroup;
the remaining content is the smooth structure and the splitting of the differential.

The theorem of this file is **Cartan's closed-subgroup theorem**: a closed subgroup of a
finite-dimensional real Lie group is an embedded Lie subgroup, with model vector space its Lie
algebra `TauCeti.Lie.lieSubalgebraOfSubgroup`.  It is what makes a group cut out of a Lie group by
closed conditions -- a matrix group, a maximal torus, the kernel or centralizer of a continuous
homomorphism -- a Lie group in its own right.

The model space being the Lie algebra pins the dimension of `K`.  The finer statement that the Lie
algebra of `K` *as a Lie group* maps isomorphically onto `lieSubalgebraOfSubgroup K` along the
differential of the inclusion is not proved here.

## Main definitions and results

* `TauCeti.Lie.EmbeddedLieSubgroupData`: a smooth structure exhibiting a subgroup as an embedded
  Lie subgroup, with a named model vector space.
* `TauCeti.Lie.IsEmbeddedLieSubgroup`: a subgroup admits such data.
* `TauCeti.Lie.nonempty_embeddedLieSubgroupData_lieSubalgebraOfSubgroup_of_isClosed`:
  **the closed-subgroup theorem with its model space**, the data for a closed subgroup with model
  space its Lie algebra.
* `TauCeti.Lie.isEmbeddedLieSubgroup_of_isClosed`: **the closed-subgroup (Cartan) theorem**.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd edition (2013), Theorem 20.12.
* J. Hilgert and K.-H. Neeb, *Structure and Geometry of Lie Groups* (2012), Section 9.1.
-/

public section

noncomputable section

universe u v w

open scoped ContDiff Manifold

namespace TauCeti.Lie

attribute [local instance] ContMDiffMul.boundarylessManifold

/-- **Embedded-Lie-subgroup data** for a subgroup `K` of a charted group `G`, with model vector
space `E'`: a smooth structure on `K`, for its subspace topology and with the boundaryless model
`𝓘(ℝ, E')`, making `K` a Lie group whose inclusion into `G` is smooth and has a split differential
everywhere.

The inclusion is a topological embedding for free, since `K` carries the subspace topology; the
split differential is the smooth half of being an embedded submanifold. -/
structure EmbeddedLieSubgroupData {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {G : Type w} [TopologicalSpace G] [ChartedSpace H G] [Group G]
    (K : Subgroup G) (E' : Type*) [NormedAddCommGroup E'] [NormedSpace ℝ E'] where
  /-- the charts of `K`, with model space `E'` -/
  [chartedSpace : ChartedSpace E' K]
  /-- the charts are smoothly compatible and the inherited group operations are smooth -/
  [lieGroup : LieGroup 𝓘(ℝ, E') ∞ K]
  /-- the inclusion into the ambient group is smooth -/
  contMDiff_subtypeVal : ContMDiff 𝓘(ℝ, E') I ∞ (fun x : K ↦ (x : G))
  /-- the differential of the inclusion has a continuous left inverse at every point -/
  isDiffImmersionAt_subtypeVal :
    ∀ k : K, IsDiffImmersionAt 𝓘(ℝ, E') I (fun x : K ↦ (x : G)) k

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type w} [TopologicalSpace G] [ChartedSpace H G] [Group G]

/-- **`K` is an embedded Lie subgroup**: it carries `TauCeti.Lie.EmbeddedLieSubgroupData` for some
model vector space.

The model space is quantified over the universe of `G`, which is where the Lie algebra of `G`
lives, exactly as Mathlib's `Manifold.IsImmersionAt` pins the universe of its complement. -/
def IsEmbeddedLieSubgroup (K : Subgroup G) : Prop :=
  ∃ (E' : Type w) (_ : NormedAddCommGroup E') (_ : NormedSpace ℝ E'),
    Nonempty (EmbeddedLieSubgroupData I K E')

variable [FiniteDimensional ℝ E] [LieGroup I ∞ G]

/-- **The closed-subgroup theorem, with its model space.** A closed subgroup of a
finite-dimensional real Lie group carries embedded-Lie-subgroup data whose model vector space is
the Lie algebra `TauCeti.Lie.lieSubalgebraOfSubgroup` of the subgroup. -/
theorem nonempty_embeddedLieSubgroupData_lieSubalgebraOfSubgroup_of_isClosed {K : Subgroup G}
    (hK : IsClosed (K : Set G)) :
    let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
    Nonempty (EmbeddedLieSubgroupData I K (lieSubalgebraOfSubgroup (I := I) K).toSubmodule) := by
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  dsimp only
  obtain ⟨q, Φ, hpq, h1, hslice, hΦ, hΦsymm⟩ :=
    exists_isSliceChart_of_isClosed_subgroup (I := I) hK
  let _ : ContinuousMul G := continuousMul_of_contMDiffMul I ∞
  exact ⟨{ chartedSpace := Subgroup.chartedSpaceOfIsSliceChart K Φ hslice h1
           lieGroup := Subgroup.lieGroup_chartedSpaceOfIsSliceChart K Φ hslice h1 hΦ hΦsymm
           contMDiff_subtypeVal :=
             Subgroup.contMDiff_subtypeVal_chartedSpaceOfIsSliceChart K Φ hslice h1 hΦsymm
           isDiffImmersionAt_subtypeVal := fun k ↦
             Subgroup.isDiffImmersionAt_subtypeVal_chartedSpaceOfIsSliceChart K Φ hslice h1 hΦ
               hΦsymm (by simp) k }⟩

/-- **The closed-subgroup (Cartan) theorem.** A closed subgroup of a finite-dimensional real Lie
group is an embedded Lie subgroup: it is a Lie group for its subspace topology, and its inclusion
is smooth with everywhere split differential. -/
theorem isEmbeddedLieSubgroup_of_isClosed {K : Subgroup G} (hK : IsClosed (K : Set G)) :
    IsEmbeddedLieSubgroup (I := I) K := by
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  have : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
    finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint
  exact ⟨(lieSubalgebraOfSubgroup (I := I) K).toSubmodule, inferInstance, inferInstance,
    nonempty_embeddedLieSubgroupData_lieSubalgebraOfSubgroup_of_isClosed hK⟩

end TauCeti.Lie
