/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Flow
public import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Compactness.Compact

/-!
# Invariant sets and basic flow lemmas

This file supplements Mathlib's `IsInvariant` predicate and `Flow` API from
`Mathlib.Dynamics.Flow`.

## Main declarations

* `IsInvariant.apply_mem_iff`: membership in a subset invariant under a family of maps with
  inverses is unchanged by each map.
* `Flow.apply_comm`: the maps of a flow by a commutative time monoid commute.
* `Flow.map_neg_apply_map`, `Flow.map_apply_map_neg`: the time-`(-t)` map undoes the time-`t` map
  and conversely.
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

/-- The time-`(-t)` map undoes the time-`t` map. -/
@[simp]
theorem map_neg_apply_map [AddGroup τ] (ϕ : Flow τ α) (t : τ) (x : α) : ϕ (-t) (ϕ t x) = x := by
  rw [← ϕ.map_add, neg_add_cancel, ϕ.map_zero_apply]

/-- The time-`t` map undoes the time-`(-t)` map. -/
@[simp]
theorem map_apply_map_neg [AddGroup τ] (ϕ : Flow τ α) (t : τ) (x : α) : ϕ t (ϕ (-t) x) = x := by
  rw [← ϕ.map_add, add_neg_cancel, ϕ.map_zero_apply]

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

/-- **Homotopy along flow lines.** Two maps into a space `Z` embedded in `α` which send each `y` to
the flow line of `p y` at the times `τ₀ y` and `τ₁ y` are homotopic, provided the flow line stays
in `Z` at the times in between. -/
theorem homotopic_of_eq_apply {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (ϕ : Flow ℝ α) {ι : Z → α} (hι : Topology.IsEmbedding ι) {F₀ F₁ : C(Y, Z)} {p : Y → α}
    (hp : Continuous p) {τ₀ τ₁ : Y → ℝ} (hτ₀ : Continuous τ₀) (hτ₁ : Continuous τ₁)
    (hF₀ : ∀ y, ι (F₀ y) = ϕ (τ₀ y) (p y)) (hF₁ : ∀ y, ι (F₁ y) = ϕ (τ₁ y) (p y))
    (hZ : ∀ y, ∀ t ∈ Set.Icc (0 : ℝ) 1, ϕ ((1 - t) * τ₀ y + t * τ₁ y) (p y) ∈ Set.range ι) :
    F₀.Homotopic F₁ := by
  choose G hG using fun q : unitInterval × Y ↦ hZ q.2 q.1 q.1.2
  refine ⟨⟨⟨G, ?_⟩, fun y ↦ ?_, fun y ↦ ?_⟩⟩
  · rw [hι.continuous_iff, Function.comp_def]
    simp_rw [hG]
    exact ϕ.continuous (by fun_prop) (hp.comp continuous_snd)
  · exact hι.injective ((hG (0, y)).trans (by simp [hF₀]))
  · exact hι.injective ((hG (1, y)).trans (by simp [hF₁]))

end Flow
