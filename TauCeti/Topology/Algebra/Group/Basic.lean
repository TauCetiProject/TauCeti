/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Basic

/-!
# Continuous multiplication on subgroups, and closed centers

A subgroup inherits continuous or separately continuous multiplication for the subspace topology.
Mathlib provides these instances for submonoids, but instance search does not see a subgroup as a
submonoid, so the subgroup instances are registered separately.

In a Hausdorff magma with separately continuous multiplication the center is closed, next to
Mathlib's `Set.isClosed_centralizer`: each defining identity of a central element is an
equality of continuous functions of it.

## Main results

* `Subgroup.separatelyContinuousMul`: a subgroup inherits `SeparatelyContinuousMul`.
* `Subgroup.continuousMul`: a subgroup inherits `ContinuousMul`, without continuity of inversion.
* `Set.isClosed_center`: the center of a Hausdorff magma with separately continuous
  multiplication is closed.
-/

public section

/-- In a Hausdorff magma with separately continuous multiplication, the center is closed. -/
theorem Set.isClosed_center (M : Type*) [Mul M] [TopologicalSpace M]
    [SeparatelyContinuousMul M] [T2Space M] : IsClosed (Set.center M) := by
  simp only [Set.center, isMulCentral_iff, commute_iff_eq, Set.ofPred_and, Set.ofPred_forall]
  refine .inter ?_ (.inter ?_ ?_) <;> repeat' refine isClosed_iInter fun _ ↦ ?_
  all_goals apply isClosed_eq <;> fun_prop

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
