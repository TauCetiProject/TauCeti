/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Discrete subgroups act properly discontinuously

A discrete subgroup `S` of a `T₁` topological group `G` is closed, so it meets every compact set
of `G` in a finite set. Hence `S` acts properly discontinuously on `G` by left multiplication.
Mathlib proves this from the hypothesis that the inclusion `S → G` tends to the cocompact filter
along the cofinite filter (`Subgroup.properlyDiscontinuousSMul_of_tendsto_cofinite`); this file
records it as an instance for subgroups carrying the discrete topology, and for discrete
submodules of a topological module acting by translation, such as a lattice in a real or complex
vector space.

## Main results

* `Subgroup.properlyDiscontinuousSMul_of_discreteTopology`,
  `AddSubgroup.properlyDiscontinuousVAdd_of_discreteTopology`: a discrete subgroup acts properly
  discontinuously on the ambient group.
* `Submodule.properlyDiscontinuousVAdd_of_discreteTopology`: a discrete submodule acts properly
  discontinuously on the ambient module by translation.
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
