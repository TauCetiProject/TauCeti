/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import TauCeti.Topology.Algebra.ConstMulAction

/-!
# Balls separated from their translates outside the stabilizer

For a properly discontinuous action on a locally compact metric space, every point `x` lies in a
ball which meets none of its translates by group elements outside the stabilizer of `x`: a group
element moving that ball to meet itself already fixes `x`.

This separation is one half of the localization of an orbit space near a point with nontrivial
stabilizer. The other half, that the ball is itself invariant under the stabilizer, does not
follow from the hypotheses here: under `ContinuousConstSMul` alone an element fixing `x` need not
preserve a ball about `x`. Once that invariance is supplied — for an isometric action, say, whose
elements fixing `x` preserve every ball about `x` — the orbit space of the whole group near `x`
agrees with the orbit space of the single stabilizer, which for a properly discontinuous action
is a finite group.

## Main results

* `TauCeti.eventually_smul_eq_self_of_image_smul_ball_inter_nonempty`: for every small enough
  ball about a point, a scalar moving a point of the ball into the ball fixes the centre.
* `TauCeti.exists_ball_disjoint_smul_of_notMem_stabilizer`: a small enough ball about a point is
  disjoint from each of its translates by a group element not fixing that point.
-/

public section

open Filter Metric MulAction Set Topology

open scoped Pointwise

namespace TauCeti

variable (G : Type*) {X : Type*} [PseudoMetricSpace X] [T2Space X]

/-- **Small balls are separated from translates that move the centre.** For a properly
discontinuous scalar action on a locally compact Hausdorff pseudo-metric space, for every small
enough `r > 0`, a scalar moving some point of the ball of radius `r` about `x` into that ball
fixes `x`. -/
theorem eventually_smul_eq_self_of_image_smul_ball_inter_nonempty [LocallyCompactSpace X]
    [SMul G X] [ContinuousConstSMul G X] [ProperlyDiscontinuousSMul G X] (x : X) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ g : G,
      ((g • ·) '' ball x r ∩ ball x r).Nonempty → g • x = x := by
  obtain ⟨U, hU, hfix⟩ := ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self G x
  filter_upwards [(eventually_ball_subset hU).filter_mono nhdsWithin_le_nhds] with r hr g hg
  exact hfix g (hg.mono (inter_subset_inter (image_mono hr) hr))

/-- **A small enough ball meets no translate of itself by an element outside the stabilizer.**
For a properly discontinuous action on a locally compact Hausdorff pseudo-metric space, some ball
about `x` is moved to meet itself only by the elements fixing `x`. -/
theorem exists_ball_disjoint_smul_of_notMem_stabilizer [LocallyCompactSpace X]
    [Group G] [MulAction G X] [ContinuousConstSMul G X] [ProperlyDiscontinuousSMul G X] (x : X) :
    ∃ r > 0, ∀ g : G, g ∉ stabilizer G x → Disjoint (g • ball x r) (ball x r) := by
  obtain ⟨r, hfix, hr⟩ :=
    ((eventually_smul_eq_self_of_image_smul_ball_inter_nonempty G x).and
      self_mem_nhdsWithin).exists
  refine ⟨r, hr, fun g hg ↦ ?_⟩
  by_contra hdis
  rw [not_disjoint_iff_nonempty_inter, ← image_smul] at hdis
  exact hg (MulAction.mem_stabilizer_iff.mpr (hfix g hdis))

end TauCeti
