/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Order.OrderClosed

/-!
# Bounds that hold up to a vanishing correction

An estimate proved by a limiting argument typically arrives with an error term attached: one shows
`v ≤ K + e i` for every `i` far enough along a filter, where `e i` vanishes in the limit.  The
result below discharges that error term in one step, turning the eventual approximate bound into
the exact bound `v ≤ K`, so that a proof need not repeat the limit argument at each estimate it
establishes.

## Main results

* `Filter.Tendsto.le_of_eventually_le_add`: if `v ≤ K + e i` eventually along `l` and `e` tends to
  `0` along `l`, then `v ≤ K`.
-/

public section

open Filter Topology

/-- **A bound holding up to a vanishing correction holds outright.**  If `v ≤ K + e i` for all `i`
in some set of the filter `l`, and `e` tends to `0` along `l`, then `v ≤ K`.

No sign condition on `v`, `K` or `e` is required. -/
theorem Filter.Tendsto.le_of_eventually_le_add {ι α : Type*} [TopologicalSpace α] [Preorder α]
    [ClosedIciTopology α] [AddZeroClass α] [ContinuousAdd α] {l : Filter ι} [l.NeBot] {e : ι → α}
    (he : Tendsto e l (𝓝 0)) {v K : α} (h : ∀ᶠ i in l, v ≤ K + e i) : v ≤ K :=
  ge_of_tendsto (by simpa using tendsto_const_nhds.add he) h
