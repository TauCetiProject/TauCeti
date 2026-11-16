/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousOn

/-!
# Relative neighbourhoods pulled back along maps continuous within a set

For a map `f : Y → X` continuous within `U` at `z`, a neighbourhood `t` of `f z` within `s` pulls
back to a neighbourhood of `z` within the part of `U` lying over `s ∩ A`, for any further set `A`
(`ContinuousWithinAt.inter_preimage_inter_mem_nhdsWithin`). For the inverse of a chart, possibly
extended through a model with corners, this lets a property of maps that is local on the domain
of a manifold be checked in the chart domains of relative neighbourhoods.
-/

public section

open Filter Set Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- **Relative neighbourhoods pulled back to a set.** For `f` continuous within `U` at `z`, a
neighbourhood `t` of `f z` within `s` pulls back to a neighbourhood of `z` within the part of `U`
lying over `s ∩ A`. -/
theorem ContinuousWithinAt.inter_preimage_inter_mem_nhdsWithin {f : Y → X} {U : Set Y}
    {s t A : Set X} {z : Y} (hf : ContinuousWithinAt f U z) (ht : t ∈ 𝓝[s] f z) :
    U ∩ f ⁻¹' (t ∩ A) ∈ 𝓝[U ∩ f ⁻¹' (s ∩ A)] z := by
  have hcont : ContinuousWithinAt f (U ∩ f ⁻¹' (s ∩ A)) z := hf.mono inter_subset_left
  have hpre : f ⁻¹' t ∈ 𝓝[U ∩ f ⁻¹' (s ∩ A)] z :=
    hcont.tendsto_nhdsWithin (fun _ hw ↦ hw.2.1) ht
  filter_upwards [self_mem_nhdsWithin, hpre] with w hw hwt
  exact ⟨hw.1, hwt, hw.2.2⟩
