/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Propagation of uniform closeness along an interval

Suppose each member of a family of maps indexed by a real interval is uniformly close to
some map with property `P`. If nearby parameters can only select the same map with property `P`,
then one such map is close to the whole family
(`TauCeti.forall_dist_lt_of_forall_exists_dist_lt`). The proof applies
`IsPreconnected.constant` to the locally constant predicate of being close to a fixed map.

This lets local estimates select a single limiting map throughout a connected parameter window.
-/

public section

open Set Filter Topology

namespace TauCeti

/-- Let `P` be a property of maps `ι → V`, and suppose that along `[p, q]` every slice of `u`
is uniformly within `e` of a map with property `P`. Suppose two such maps near slices at
parameters at most `η > 0` apart coincide. Then a map with property `P` near the slice at `p`
is near every slice along `[p, q]`: closeness is locally constant along the interval. -/
theorem forall_dist_lt_of_forall_exists_dist_lt {ι V : Type*} [PseudoMetricSpace V]
    {u : ℝ × ι → V} {P : (ι → V) → Prop} {p q e η : ℝ}
    (hη : 0 < η)
    (hnear : ∀ s ∈ Icc p q, ∃ y, P y ∧ ∀ t, dist (u (s, t)) (y t) < e)
    (hsame : ∀ s ∈ Icc p q, ∀ s' ∈ Icc p q, |s - s'| ≤ η → ∀ y y', P y → P y' →
      (∀ t, dist (u (s, t)) (y t) < e) → (∀ t, dist (u (s', t)) (y' t) < e) → y = y')
    {x : ι → V} (hx : P x) (hxd : ∀ t, dist (u (p, t)) (x t) < e) :
    ∀ s ∈ Icc p q, ∀ t, dist (u (s, t)) (x t) < e := by
  classical
  set f : ℝ → Bool := fun s ↦ decide (∀ t, dist (u (s, t)) (x t) < e)
  have hf (s : ℝ) (hs : s ∈ Icc p q) (y : ι → V) (hy : P y)
      (hyd : ∀ t, dist (u (s, t)) (y t) < e) : f s = true ↔ x = y :=
    ⟨fun h ↦ hsame s hs s hs (by simpa using hη.le) x y hx hy (of_decide_eq_true h) hyd,
      fun h ↦ decide_eq_true (h ▸ hyd)⟩
  have hcont : ContinuousOn f (Icc p q) := fun s hs ↦ by
    rw [ContinuousWithinAt, nhds_discrete, tendsto_pure]
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Metric.closedBall_mem_nhds s hη)] with s' hs' hball
    obtain ⟨y, hy, hyd⟩ := hnear s hs
    obtain ⟨y', hy', hy'd⟩ := hnear s' hs'
    have hyy' : y' = y := hsame s' hs' s hs (by rwa [← Real.dist_eq]) y' y hy' hy hy'd hyd
    rw [Bool.eq_iff_iff, hf s' hs' y' hy' hy'd, hf s hs y hy hyd, hyy']
  intro s hs
  exact of_decide_eq_true
    ((isPreconnected_Icc.constant hcont hs ⟨le_rfl, hs.1.trans hs.2⟩).trans (decide_eq_true hxd))

end TauCeti
