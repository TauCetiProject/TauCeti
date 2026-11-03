/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Bundle

/-!
# Fibre-preserving maps of total spaces

A map of total spaces `Bundle.TotalSpace F₁ E₁ → Bundle.TotalSpace F₂ E₂` covering the identity of
the base is determined by its fibre maps `E₁ x → E₂ x`. It is bijective exactly when each of
its fibre maps is (`TauCeti.bijective_totalSpace_map_iff`). No topology or linear structure is
involved.
-/

public section

open Bundle

namespace TauCeti

/-- A fibre-preserving map of total spaces is bijective exactly when each of its fibre maps is. -/
theorem bijective_totalSpace_map_iff {B F₁ F₂ : Type*} {E₁ E₂ : B → Type*}
    {ϕ : ∀ x, E₁ x → E₂ x} :
    Function.Bijective (fun p : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₂ p.proj (ϕ p.proj p.2)) ↔
      ∀ x, Function.Bijective (ϕ x) := by
  refine ⟨fun h x ↦ ⟨fun v w hvw ↦ TotalSpace.mk_inj.1 (h.1 (by simp [hvw])), fun w ↦ ?_⟩,
    fun h ↦ ⟨fun ⟨x, v⟩ ⟨y, w⟩ hvw ↦ ?_, fun ⟨x, w⟩ ↦ ⟨⟨x, (h x).2 w |>.choose⟩, ?_⟩⟩⟩
  · obtain ⟨⟨y, v⟩, hp⟩ := h.2 ⟨x, w⟩
    obtain rfl : y = x := congrArg TotalSpace.proj hp
    exact ⟨v, TotalSpace.mk_inj.1 hp⟩
  · obtain rfl : x = y := congrArg TotalSpace.proj hvw
    simp only [TotalSpace.mk_inj] at hvw
    rw [(h x).1 hvw]
  · simp [((h x).2 w).choose_spec]

end TauCeti
