/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Maps.Basic

/-!
# Open maps from continuous local sections

A map is open if it has a continuous local section through every point of its domain.
The section identity is needed only near the image point; neither global sections nor
continuity of the original map is required. This applies in particular to the source map
of a groupoid with local bisections.
-/

public section

open Filter Topology

namespace IsOpenMap

/-- A map with a continuous local section through every domain point is open.
The local section may be extended arbitrarily outside its neighborhood of definition. -/
theorem of_local_sections {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y}
    (h : ∀ x, ∃ σ : Y → X, ContinuousAt σ (f x) ∧ σ (f x) = x ∧
      (∀ᶠ y in 𝓝 (f x), f (σ y) = y)) : IsOpenMap f := by
  apply of_nhds_le
  intro x
  obtain ⟨σ, hσ, hx, hsec⟩ := h x
  have hmap : map f (map σ (𝓝 (f x))) = 𝓝 (f x) := by
    calc
      _ = map id (𝓝 (f x)) := by rw [map_map]; exact map_congr hsec
      _ = _ := map_id
  rw [ContinuousAt, hx] at hσ
  rw [← hmap]
  exact map_mono hσ

end IsOpenMap
