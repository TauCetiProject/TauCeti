/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Monoid

/-!
# Separately continuous multiplication on subgroups

A subgroup of a group with separately continuous multiplication has separately continuous
multiplication for the subspace topology. Mathlib provides this for submonoids, but instance
search does not see a subgroup as a submonoid, so the subgroup instance is registered separately.

## Main results

* `Subgroup.separatelyContinuousMul`: a subgroup inherits `SeparatelyContinuousMul`.
-/

public section

/-- A subgroup of a group with separately continuous multiplication has separately continuous
multiplication. -/
@[to_additive /-- An additive subgroup of an additive group with separately continuous addition has
separately continuous addition. -/]
instance Subgroup.separatelyContinuousMul {G : Type*} [TopologicalSpace G] [Group G]
    [SeparatelyContinuousMul G] (S : Subgroup G) : SeparatelyContinuousMul S :=
  S.toSubmonoid.separatelyContinuousMul
