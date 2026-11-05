/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Flow

/-!
# Invariant sets and basic flow lemmas

This file supplements Mathlib's `IsInvariant` predicate and `Flow` API from
`Mathlib.Dynamics.Flow`.

## Main declarations

* `IsInvariant.apply_mem_iff`: membership in a subset invariant under a family of maps with
  inverses is unchanged by each map.
* `Flow.apply_comm`: the maps of a flow by a commutative time monoid commute.
* `Flow.orbit_apply`: flowing a point does not change its orbit.
* `Flow.map_sub_apply_map_sub_apply`: flowing for time `t - u` and then `u - t` is the identity.
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

namespace Flow

variable {τ α : Type*} [TopologicalSpace τ] [TopologicalSpace α]

/-- The maps of a flow by a commutative time monoid commute. -/
theorem apply_comm [AddCommMonoid τ] (ϕ : Flow τ α) (s t : τ) (x : α) :
    ϕ s (ϕ t x) = ϕ t (ϕ s x) := by
  rw [← map_add, add_comm, map_add]

/-- All points of an orbit have the same orbit. -/
@[simp]
theorem orbit_apply [AddGroup τ] (ϕ : Flow τ α) (s : τ) (x : α) : orbit ϕ (ϕ s x) = orbit ϕ x :=
  @AddAction.orbit_vadd τ α _ ϕ.toAddAction s x

/-- Flowing for time `t - u` and then for time `u - t` returns every point to where it started. -/
theorem map_sub_apply_map_sub_apply [AddGroup τ] (ϕ : Flow τ α) (t u : τ) (x : α) :
    ϕ (u - t) (ϕ (t - u) x) = x := by
  rw [← map_add, sub_add_sub_cancel, sub_self, map_zero_apply]

end Flow
