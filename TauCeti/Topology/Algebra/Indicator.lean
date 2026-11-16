/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Indicator
public import Mathlib.Topology.Separation.Basic

/-!
# Continuity of indicator functions away from the frontier

The indicator of a set `s` of a function continuous on the interior of `s` is continuous at every
point off the frontier of `s` (`ContinuousOn.continuousAt_indicator`), hence continuous on every
set disjoint from the frontier. Applied to a spectrum, this is the continuity of the indicator
that the continuous functional calculus needs to define a spectral projection.

The frontier of `s` may also meet `t`, as long as `s` lies in a set `u` whose frontier avoids `t`
and which meets `t` in finitely many points: then every point of `t ∩ u` is isolated in `t`, and
the indicator vanishes near every other point of `t`. For a spectrum `t`, this covers the
indicator of `[0, c]` when only finitely many spectral values lie in `[-c, c]`.

## Main results

* `ContinuousOn.continuousOn_mulIndicator_of_disjoint_frontier`,
  `ContinuousOn.continuousOn_indicator_of_disjoint_frontier`: the indicator `s.indicator f` is
  continuous on every set disjoint from `frontier s`.
* `Set.Finite.continuousOn_mulIndicator`, `Set.Finite.continuousOn_indicator`: the indicator
  `s.indicator f` is continuous on `t` if `s ⊆ u`, the frontier of `u` avoids `t`, and `t ∩ u` is
  finite.
-/

public section

open Filter Topology

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] [One β] {f : α → β}
  {s t : Set α}

/-- The multiplicative indicator `s.mulIndicator f` of a function continuous on the interior of `s`
is continuous on every set disjoint from the frontier of `s`. -/
@[to_additive /-- The indicator `s.indicator f` of a function continuous on the interior of `s` is
continuous on every set disjoint from the frontier of `s`. -/]
theorem ContinuousOn.continuousOn_mulIndicator_of_disjoint_frontier
    (hf : ContinuousOn f (interior s)) (ht : Disjoint (frontier s) t) :
    ContinuousOn (s.mulIndicator f) t := fun _ hx ↦
  (hf.continuousAt_mulIndicator (ht.notMem_of_mem_right hx)).continuousWithinAt

/-- The multiplicative indicator `s.mulIndicator f` is continuous on `t` if `s` lies in a set `u`
whose frontier avoids `t` and which meets `t` in finitely many points. -/
@[to_additive /-- The indicator `s.indicator f` is continuous on `t` if `s` lies in a set `u` whose
frontier avoids `t` and which meets `t` in finitely many points. -/]
theorem Set.Finite.continuousOn_mulIndicator [T1Space α] {u : Set α} (hfin : (t ∩ u).Finite)
    (hsu : s ⊆ u) (ht : Disjoint (frontier u) t) : ContinuousOn (s.mulIndicator f) t := by
  intro x hx
  by_cases hxu : x ∈ closure u
  · -- `x` is in the interior of `u`, which meets `t` in finitely many points: it is isolated.
    have hxi : x ∈ interior u := by
      by_contra h
      exact ht.notMem_of_mem_right hx ⟨hxu, h⟩
    have hfin' : ((t ∩ u) \ {x}).Finite := hfin.sdiff
    have hev : ∀ᶠ y in 𝓝[t] x, y = x := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (inter_mem
        (mem_interior_iff_mem_nhds.1 hxi) (hfin'.isClosed.compl_mem_nhds (by simp)))]
        with y hyt hy
      by_contra hne
      exact hy.2 ⟨⟨hyt, hy.1⟩, hne⟩
    exact continuousWithinAt_const.congr_of_eventuallyEq
      (hev.mono fun y hy ↦ by rw [hy]) rfl
  · -- Away from the closure of `u` the indicator is `1`.
    have hev : ∀ᶠ y in 𝓝[t] x, s.mulIndicator f y = 1 := by
      filter_upwards [nhdsWithin_le_nhds (isClosed_closure.compl_mem_nhds hxu)] with y hy
      exact Set.mulIndicator_of_notMem (fun hys ↦ hy (subset_closure (hsu hys))) f
    exact continuousWithinAt_const.congr_of_eventuallyEq hev
      (Set.mulIndicator_of_notMem (fun hxs ↦ hxu (subset_closure (hsu hxs))) f)
