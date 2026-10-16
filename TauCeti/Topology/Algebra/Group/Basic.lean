/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Monoid

/-!
# Continuous multiplication on subgroups

A subgroup inherits continuous or separately continuous multiplication for the subspace topology.
Mathlib provides these instances for submonoids, but instance search does not see a subgroup as a
submonoid, so the subgroup instances are registered separately.

## Main results

* `Subgroup.separatelyContinuousMul`: a subgroup inherits `SeparatelyContinuousMul`.
* `Subgroup.continuousMul`: a subgroup inherits `ContinuousMul`, without continuity of inversion.
-/

public section

/-- A subgroup of a group with continuous multiplication has continuous multiplication. -/
@[to_additive /-- An additive subgroup of an additive group with continuous addition has
continuous addition. -/]
instance Subgroup.continuousMul {G : Type*} [TopologicalSpace G] [Group G]
    [ContinuousMul G] (S : Subgroup G) : ContinuousMul S :=
  S.toSubmonoid.continuousMul

/-- A subgroup of a group with separately continuous multiplication has separately continuous
multiplication. -/
@[to_additive /-- An additive subgroup of an additive group with separately continuous addition has
separately continuous addition. -/]
instance Subgroup.separatelyContinuousMul {G : Type*} [TopologicalSpace G] [Group G]
    [SeparatelyContinuousMul G] (S : Subgroup G) : SeparatelyContinuousMul S :=
  S.toSubmonoid.separatelyContinuousMul
