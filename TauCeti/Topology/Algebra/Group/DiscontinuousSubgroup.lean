/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Algebra.IsUniformGroup.DiscreteSubgroup
public import Mathlib.Topology.Algebra.OpenSubgroup
public import TauCeti.Algebra.Module.Submodule.OrbitRelQuotient

/-!
# Discrete subgroups act properly discontinuously and have infinite index

A discrete subgroup `S` of a `T₁` topological group `G` is closed, so it meets every compact set
of `G` in a finite set. Hence `S` acts properly discontinuously on `G` by left multiplication.
Mathlib proves this from the hypothesis that the inclusion `S → G` tends to the cocompact filter
along the cofinite filter (`Subgroup.properlyDiscontinuousSMul_of_tendsto_cofinite`); this file
records it as an instance for subgroups carrying the discrete topology, and for discrete
submodules of a topological module acting by translation, such as a lattice in a real or complex
vector space.

A discrete subgroup of finite index in a Hausdorff topological group makes the whole group
discrete (`Subgroup.discreteTopology_iff_of_finiteIndex`). So when the group has no isolated
points, for instance a nonzero real or complex vector space, every discrete subgroup has infinite
index. In particular the orbit space of translation by a discrete submodule, such as a complex
torus `E / L` with `E ≠ 0`, is infinite.

## Main results

* `Subgroup.properlyDiscontinuousSMul_of_discreteTopology`,
  `AddSubgroup.properlyDiscontinuousVAdd_of_discreteTopology`: a discrete subgroup acts properly
  discontinuously on the ambient group.
* `Submodule.properlyDiscontinuousVAdd_of_discreteTopology`: a discrete submodule acts properly
  discontinuously on the ambient module by translation.
* `Subgroup.infinite_quotient_of_discreteTopology`,
  `AddSubgroup.infinite_quotient_of_discreteTopology`: a discrete subgroup of a Hausdorff group
  without isolated points has infinite index.
* `Submodule.instInfiniteOrbitRelQuotient`: the orbit space of translation by a discrete
  submodule of a Hausdorff topological module without isolated points is infinite.
-/

public section

/-- A discrete subgroup of a `T₁` topological group acts properly discontinuously on the group by
left multiplication. -/
@[to_additive /-- A discrete additive subgroup of a `T₁` additive topological group acts properly
discontinuously on the group by translation. -/]
instance Subgroup.properlyDiscontinuousSMul_of_discreteTopology {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T1Space G] (S : Subgroup G) [DiscreteTopology S] :
    ProperlyDiscontinuousSMul S G :=
  S.properlyDiscontinuousSMul_of_tendsto_cofinite <|
    S.tendsto_coe_cofinite_of_isDiscrete <| isDiscrete_iff_discreteTopology.2 ‹_›

/-- A discrete submodule of a `T₁` topological module acts properly discontinuously on the module
by translation. -/
instance Submodule.properlyDiscontinuousVAdd_of_discreteTopology {R M : Type*} [Ring R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [T1Space M]
    (p : Submodule R M) [DiscreteTopology p] : ProperlyDiscontinuousVAdd p M :=
  AddSubgroup.properlyDiscontinuousVAdd_of_discreteTopology p.toAddSubgroup

open scoped Topology in
/-- **A discrete subgroup of a group without isolated points has infinite index.** A discrete
subgroup of finite index in a Hausdorff topological group makes the group itself discrete
(`Subgroup.discreteTopology_iff_of_finiteIndex`). -/
@[to_additive /-- **A discrete subgroup of an additive group without isolated points has infinite
index.** A discrete subgroup of finite index in a Hausdorff additive topological group makes the
group itself discrete (`AddSubgroup.discreteTopology_iff_of_finiteIndex`). -/]
theorem Subgroup.infinite_quotient_of_discreteTopology {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [(𝓝[≠] (1 : G)).NeBot] (H : Subgroup G)
    [DiscreteTopology H] : Infinite (G ⧸ H) := by
  refine not_finite_iff_infinite.mp fun _ ↦ ?_
  have := H.finiteIndex_of_finite_quotient
  have := H.discreteTopology_iff_of_finiteIndex.mp ‹_›
  exact not_isOpen_singleton (1 : G) (isOpen_discrete _)

open scoped Topology in
/-- The orbit space of translation by a discrete submodule of a Hausdorff topological module
without isolated points is infinite, since the submodule has infinite index
(`AddSubgroup.infinite_quotient_of_discreteTopology`). For instance, a complex torus `E / L` with
`E ≠ 0` is infinite. -/
instance Submodule.instInfiniteOrbitRelQuotient {R M : Type*} [Ring R] [AddCommGroup M]
    [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [T2Space M]
    [(𝓝[≠] (0 : M)).NeBot] (p : Submodule R M) [DiscreteTopology p] :
    Infinite (AddAction.orbitRel.Quotient p M) :=
  -- `M ⧸ p` is by definition `M ⧸ p.toAddSubgroup`, as in Mathlib's instances on `M ⧸ p`.
  have : Infinite (M ⧸ p) := p.toAddSubgroup.infinite_quotient_of_discreteTopology
  p.orbitRelQuotientAddEquiv.toEquiv.infinite_iff.mpr this
