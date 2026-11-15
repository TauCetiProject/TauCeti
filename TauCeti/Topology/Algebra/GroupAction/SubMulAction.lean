/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.IsUniformGroup.DiscreteSubgroup
public import TauCeti.Algebra.GroupAction.OrbitRelQuotient

/-!
# Discrete stabilizers on invariant subsets

Let a topological group `G` act on `X`, let `H` be a subgroup of `G` and `S` an `H`-invariant
subset of `X`. If the stabilizer in `G` of a point `s` of `S` lies in `H`, then the stabilizer of
`s` in `H` is homeomorphic to its stabilizer in `G`, so one is discrete exactly when the other is
(`SubMulAction.discreteTopology_stabilizer_iff`). This is the locally free counterpart of
`SubMulAction.stabilizer_eq_bot_iff`.
-/

public section

namespace SubMulAction

open MulAction

variable {G X : Type*} [Group G] [TopologicalSpace G] [MulAction G X] {H : Subgroup G}
  (S : SubMulAction H X)

/-- **Local freeness on an invariant subset.** If the stabilizer in `G` of a point `s` of `S` lies
in `H`, then `s` has discrete stabilizer in `H` exactly when it has discrete stabilizer in `G`. -/
theorem discreteTopology_stabilizer_iff {s : S} (hle : stabilizer G (s : X) ≤ H) :
    DiscreteTopology (stabilizer H s) ↔ DiscreteTopology (stabilizer G (s : X)) := by
  rw [S.stabilizer_eq_subgroupOf]
  exact (Subgroup.subgroupOfContinuousMulEquivOfLe hle).discreteTopology_iff

end SubMulAction
