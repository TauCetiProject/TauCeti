/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Separation.Hausdorff

/-!
# Extending local identities from dense sets

Two maps into a Hausdorff space that are continuous near a point and agree near that point
within a dense set agree on a full neighborhood. In particular, this extends identities
across a coordinate hyperplane when its complement is dense.
-/

public section

open Filter Set Topology

/-- Maps that are continuous near a point and agree near it within a dense set agree
on a full neighborhood of the point. -/
theorem Dense.eventuallyEq_nhds {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] {s : Set X} {x : X} {f g : X → Y} (hs : Dense s)
    (hf : ∀ᶠ z in 𝓝 x, ContinuousAt f z) (hg : ∀ᶠ z in 𝓝 x, ContinuousAt g z)
    (hfg : f =ᶠ[𝓝[s] x] g) : f =ᶠ[𝓝 x] g := by
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp
    ((eventually_nhdsWithin_iff.mp hfg).and (hf.and hg))
  have hEq : EqOn f g (U ∩ s) := fun z hz ↦ (hUsub hz.1).1 hz.2
  exact Filter.mem_of_superset (hU.mem_nhds hxU) (hEq.of_subset_closure
    (fun z hz ↦ (hUsub hz).2.1.continuousWithinAt)
    (fun z hz ↦ (hUsub hz).2.2.continuousWithinAt)
    inter_subset_left (hs.open_subset_closure_inter hU))
