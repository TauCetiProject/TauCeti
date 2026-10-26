/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Flow

/-!
# Invariant sets

This file supplements Mathlib's `IsInvariant` predicate from `Mathlib.Dynamics.Flow`.

## Main declarations

* `IsInvariant.apply_mem_iff`: membership in a subset invariant under a family of maps with
  inverses is unchanged by each map.
-/

public section

namespace TauCeti

/-- Membership in a subset invariant under a family of maps with inverses is unchanged by each
map. -/
theorem _root_.IsInvariant.apply_mem_iff {G X : Type*} [Inv G] {ϕ : G → X → X} {s : Set X}
    (hs : IsInvariant ϕ s) (hϕ : ∀ g x, ϕ g⁻¹ (ϕ g x) = x) (g : G) (x : X) :
    ϕ g x ∈ s ↔ x ∈ s :=
  ⟨fun h ↦ hϕ g x ▸ hs g⁻¹ h, fun h ↦ hs g h⟩

end TauCeti
