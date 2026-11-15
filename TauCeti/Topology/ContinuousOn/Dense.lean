/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Separation.Hausdorff

/-!
# Extending local identities from locally dense sets

Two maps into a Hausdorff space that agree near a point `x` within a set `s` whose closure is a
neighbourhood of `x`, and that are continuous within `s` at every point near `x`, agree on a full
neighbourhood of `x`. This is a germ-level analogue of `Set.EqOn.of_subset_closure`. For
example, it extends identities across a coordinate hyperplane whose complement is dense.
-/

public section

open Topology

/-- Maps into a Hausdorff space that agree near `x` within a set `s` whose closure is a
neighbourhood of `x`, and that are continuous within `s` at every point near `x`, agree on a full
neighbourhood of `x`. -/
theorem Filter.EventuallyEq.eventuallyEq_nhds_of_closure_mem_nhds {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] {s : Set X} {x : X} {f g : X → Y}
    (hfg : f =ᶠ[𝓝[s] x] g) (hs : closure s ∈ 𝓝 x)
    (hf : ∀ᶠ z in 𝓝 x, ContinuousWithinAt f s z) (hg : ∀ᶠ z in 𝓝 x, ContinuousWithinAt g s z) :
    f =ᶠ[𝓝 x] g := by
  filter_upwards [hs, hf, hg, (eventually_nhdsWithin_iff.mp hfg).eventually_nhds]
    with z hzs hfz hgz hz
  have := mem_closure_iff_nhdsWithin_neBot.mp hzs
  exact tendsto_nhds_unique_of_eventuallyEq hfz hgz (eventually_nhdsWithin_iff.mpr hz)
