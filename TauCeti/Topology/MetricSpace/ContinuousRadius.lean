/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.PartitionOfUnity
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.Metrizable.Uniformity

/-!
# Continuous radii subordinate to a cover

A map inducing the topology from a pseudometric space admits a positive continuous radius.
For each source point `x`, the preimage of the ball around `f x` with twice the chosen
radius lies in one member of a prescribed open cover of the source. The radius can also
be bounded by a positive constant assigned to that member. No local finiteness of the
given cover or compactness of the source space is required.

This combines Mathlib's convex-valued partition-of-unity selection theorem
`exists_continuous_forall_mem_convex_of_local_const` with metric balls. In tubular
neighbourhood arguments, comparing the larger of two radii puts both base points
in a single local injectivity neighbourhood.

Reference: J. M. Lee, *Introduction to Smooth Manifolds*, second edition,
Theorem 6.24, the variable-radius shrinking argument.
-/

public section

open Set Filter Topology

namespace Topology.IsInducing

variable {X Y ι : Type*} [TopologicalSpace X] [PseudoMetricSpace Y] {f : X → Y}

/-- Choose positive continuous radii subordinate to an open cover of the source space.
At each point, one cover member contains every point whose image is within twice the
chosen radius, and its assigned positive bound exceeds that radius. -/
theorem exists_continuous_radius_subordinate (hf : IsInducing f)
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i)) (hcov : ∀ x, ∃ i, x ∈ U i)
    (ε : ι → ℝ) (hε : ∀ i, 0 < ε i) :
    ∃ r : C(X, ℝ), (∀ x, 0 < r x) ∧ ∀ x, ∃ i, x ∈ U i ∧ r x < ε i ∧
      ∀ y, dist (f x) (f y) < 2 * r x → y ∈ U i := by
  let := hf.pseudoMetrizableSpace
  let := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X
  -- At each point the admissible radii form an interval: shrinking preserves admissibility.
  let T : X → Set ℝ := fun x => {r | 0 < r ∧ ∃ i, x ∈ U i ∧ r < ε i ∧
    ∀ y, dist (f x) (f y) < 2 * r → y ∈ U i}
  have hT : ∀ x, Convex ℝ (T x) := by
    intro x
    apply Set.OrdConnected.convex
    constructor
    rintro a ⟨ha, -⟩ b ⟨-, i, hxi, hb, hball⟩ c ⟨hac, hcb⟩
    exact ⟨ha.trans_le hac, i, hxi, hcb.trans_lt hb,
      fun y hy => hball y (hy.trans_le (mul_le_mul_of_nonneg_left hcb (by norm_num)))⟩
  have hlocal : ∀ x, ∃ c : ℝ, ∀ᶠ y in 𝓝 x, c ∈ T y := by
    intro x
    obtain ⟨i, hxi⟩ := hcov x
    obtain ⟨O, hO, hpre⟩ := hf.isOpen_iff.mp (hU i)
    have hxO : f x ∈ O := by simpa only [← hpre, mem_preimage] using hxi
    obtain ⟨d, hd, hball⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hxO)
    let c := min (d / 4) (ε i / 2)
    have hc : 0 < c := lt_min (by positivity) (half_pos (hε i))
    have hcd : c ≤ d / 4 := min_le_left _ _
    have hcε : c < ε i := (min_le_right _ _).trans_lt (half_lt_self (hε i))
    refine ⟨c, ?_⟩
    filter_upwards [hf.continuous.continuousAt.preimage_mem_nhds
      (Metric.ball_mem_nhds (f x) hc)] with y hy
    have hyx : dist (f y) (f x) < c := hy
    have hyU : y ∈ U i := by
      rw [← hpre]
      apply hball
      exact hyx.trans_le (by linarith)
    refine ⟨hc, i, hyU, hcε, fun z hz => ?_⟩
    rw [← hpre]
    apply hball
    have hzy : dist (f z) (f y) < 2 * c := by simpa [dist_comm] using hz
    have := dist_triangle (f z) (f y) (f x)
    have := add_lt_add hzy hyx
    simp only [Metric.mem_ball]
    linarith
  obtain ⟨r, hr⟩ := exists_continuous_forall_mem_convex_of_local_const hT hlocal
  exact ⟨r, fun x => (hr x).1, fun x => (hr x).2⟩

end Topology.IsInducing
