/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Flow
import Mathlib.Topology.Compactness.Compact

/-!
# Invariant sets and basic flow lemmas

This file supplements Mathlib's `IsInvariant` predicate and `Flow` API from
`Mathlib.Dynamics.Flow`.

## Main declarations

* `IsInvariant.apply_mem_iff`: membership in a subset invariant under a family of maps with
  inverses is unchanged by each map.
* `Flow.apply_comm`: the maps of a flow by a commutative time monoid commute.
* `Flow.orbit_apply`: flowing a point does not change its orbit.
* `Flow.orbit_reverse`: reversing time does not change the orbits.
* `Flow.exists_forall_exists_mem_Ioo_apply_mem`: if the forward orbits of the points of a compact
  set all meet an open set, they all meet it before a common time.
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

/-- Reversing time does not change the orbits of a flow. -/
@[simp]
theorem _root_.Flow.orbit_reverse [SubtractionCommMonoid τ] [ContinuousNeg τ] (ϕ : Flow τ α)
    (x : α) : ϕ.reverse.orbit x = ϕ.orbit x := by
  ext y
  simp only [Flow.mem_orbit_iff, Flow.reverse_apply]
  exact ⟨fun ⟨t, ht⟩ ↦ ⟨-t, ht⟩, fun ⟨t, ht⟩ ↦ ⟨-t, by rwa [neg_neg]⟩⟩

/-- **A uniform time to reach an open set.** If the forward orbit of every point of a compact set
`C` meets an open set `W` at some positive time, then there is one time `T` such that each of these
orbits meets `W` at some time in `(0, T)`. -/
theorem exists_forall_exists_mem_Ioo_apply_mem [AddMonoid τ] [LinearOrder τ] [NoMaxOrder τ]
    (ϕ : Flow τ α) {C W : Set α} (hC : IsCompact C) (hW : IsOpen W)
    (h : ∀ x ∈ C, ∃ t > 0, ϕ t x ∈ W) : ∃ T, ∀ x ∈ C, ∃ σ ∈ Set.Ioo 0 T, ϕ σ x ∈ W := by
  have hU : ∀ T : τ, IsOpen {x | ∃ σ ∈ Set.Ioo 0 T, ϕ σ x ∈ W} := fun T ↦ by
    have hset : {x | ∃ σ ∈ Set.Ioo 0 T, ϕ σ x ∈ W} = ⋃ σ ∈ Set.Ioo 0 T, ϕ σ ⁻¹' W := by
      ext
      simp
    rw [hset]
    exact isOpen_biUnion fun σ _ ↦ hW.preimage (ϕ.continuous_toFun σ)
  refine hC.elim_directed_cover _ hU (fun x hx ↦ ?_)
    (Monotone.directed_le fun T T' hT x ⟨σ, hσ, hσW⟩ ↦ ⟨σ, ⟨hσ.1, hσ.2.trans_le hT⟩, hσW⟩)
  obtain ⟨σ, hσ, hσW⟩ := h x hx
  obtain ⟨T, hT⟩ := exists_gt σ
  exact Set.mem_iUnion.2 ⟨T, σ, ⟨hσ, hT⟩, hσW⟩

end Flow
