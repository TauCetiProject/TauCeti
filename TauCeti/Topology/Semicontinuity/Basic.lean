/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Lower semicontinuity of suprema over neighbourhoods

A function of the form `x ↦ ⨆ s ∈ 𝓝 x, G s`, for an arbitrary `G : Set X → β` with values in a
complete linear order, is lower semicontinuous (`TauCeti.lowerSemicontinuous_iSup_nhds`): a strict
lower bound witnessed by a neighbourhood of `x` is witnessed by the same set at every point of its
interior. Lower envelopes and lower and upper Γ-limits are of this form.
-/

public section

open Set Topology

namespace TauCeti

variable {X β : Type*} [TopologicalSpace X] [CompleteLinearOrder β]

/-- A function of the form `x ↦ ⨆ s ∈ 𝓝 x, G s` is lower semicontinuous. -/
theorem lowerSemicontinuous_iSup_nhds (G : Set X → β) :
    LowerSemicontinuous fun x ↦ ⨆ s ∈ 𝓝 x, G s := by
  intro x c hc
  obtain ⟨s, hcs⟩ := lt_iSup_iff.1 hc
  obtain ⟨hs, hcs⟩ := lt_iSup_iff.1 hcs
  filter_upwards [interior_mem_nhds.2 hs] with y hy
  exact hcs.trans_le (le_iSup₂ (f := fun s (_ : s ∈ 𝓝 y) ↦ G s) s (mem_interior_iff_mem_nhds.1 hy))

end TauCeti
