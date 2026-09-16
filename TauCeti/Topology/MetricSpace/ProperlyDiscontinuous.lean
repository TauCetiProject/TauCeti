/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.IsometricSMul
public import TauCeti.Topology.Algebra.ConstMulAction

/-!
# Precisely invariant balls for a properly discontinuous action

For a properly discontinuous action on a locally compact metric space, every point `x` lies in a
ball which is *precisely invariant* under the stabilizer of `x`: a group element moving that ball
to meet itself already fixes `x`.

This fact helps localize an orbit space near a point with nontrivial stabilizer: on a
precisely invariant ball the orbit space of the whole group agrees with the orbit space of the
single stabilizer, which for a properly discontinuous action is a finite group.

## Main results

* `TauCeti.exists_ball_disjoint_smul_of_notMem_stabilizer`: a small enough ball about a point is
  precisely invariant under the stabilizer of that point.
-/

public section

open Metric MulAction

open scoped Pointwise

namespace TauCeti

variable (G : Type*) {X : Type*} [Group G] [MetricSpace X] [MulAction G X]

/-- **A small enough ball is precisely invariant.** For a properly discontinuous action on a
locally compact Hausdorff metric space, some ball about `x` is moved to meet itself only by the
elements fixing `x`. -/
theorem exists_ball_disjoint_smul_of_notMem_stabilizer [LocallyCompactSpace X]
    [ContinuousConstSMul G X] [ProperlyDiscontinuousSMul G X] (x : X) :
    ∃ r > 0, ∀ g : G, g ∉ stabilizer G x → Disjoint (g • ball x r) (ball x r) := by
  obtain ⟨U, hU, hfix⟩ := ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self G x
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨r, hr, fun g hg ↦ ?_⟩
  by_contra hdis
  rw [Set.not_disjoint_iff_nonempty_inter, ← Set.image_smul] at hdis
  exact hg (mem_stabilizer_iff.mpr
    (hfix g (hdis.mono (Set.inter_subset_inter (Set.image_mono hrU) hrU))))

end TauCeti
