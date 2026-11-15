/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.FiberBundle.Basic
public import Mathlib.Topology.TietzeExtension

/-!
# Extending the coordinates of a section in a trivialization

If the model fibre `F` of a fibre bundle over a normal base `B` has the Tietze extension
property, the coordinates in a trivialization `e` of a section which is continuous on a closed set
`s` extend, from `s ∩ u` for any closed `u` inside the base set of `e`, to a continuous map
`B → F` (`TauCeti.exists_continuousMap_eq_trivialization_of_continuousOn`).
-/

public section

open Bundle Set Function

namespace TauCeti

universe u w

variable {B : Type u} [TopologicalSpace B] [NormalSpace B] {F : Type w} [TopologicalSpace F]
  [TietzeExtension.{u, w} F] {E : B → Type*} [TopologicalSpace (TotalSpace F E)]

/-- A section which is continuous on a closed set `s` has, in a trivialization `e`, coordinates
extending to a continuous map `B → F` on `s ∩ u`, for `u` closed and contained in the base set
of `e`. -/
theorem exists_continuousMap_eq_trivialization_of_continuousOn {s u : Set B}
    (hs : IsClosed s) {σ : ∀ x, E x}
    (hσ : ContinuousOn (fun x ↦ TotalSpace.mk' F x (σ x)) s) (e : Trivialization F (π F E))
    (hu : IsClosed u) (hue : u ⊆ e.baseSet) :
    ∃ g : C(B, F), ∀ x ∈ s ∩ u, g x = (e ⟨x, σ x⟩).2 := by
  have hc : ContinuousOn (fun x ↦ (e ⟨x, σ x⟩).2) (s ∩ u) :=
    continuous_snd.comp_continuousOn <| e.continuousOn.comp (hσ.mono inter_subset_left)
      fun x hx ↦ e.mem_source.2 (hue hx.2)
  obtain ⟨g, hg⟩ := ContinuousMap.exists_restrict_eq (hs.inter hu) ⟨_, hc.domRestrict⟩
  exact ⟨g, fun x hx ↦ congr($hg ⟨x, hx⟩)⟩

end TauCeti
