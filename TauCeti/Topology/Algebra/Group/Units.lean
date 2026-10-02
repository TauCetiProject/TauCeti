/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Algebra.Group.Units

/-!
# Neighbourhoods, σ-compactness and preconnected sets in a group of units

The units `Mˣ` of a topological monoid `M` carry the topology induced by `u ↦ (u, u⁻¹)`.  This
file records three consequences of that definition.

* The neighbourhood filter of a unit `u` is the meet of the pullbacks of the neighbourhood filters
  of `u` and of `u⁻¹` along the coercion and the inverse coercion.  Concretely, a set is a
  neighbourhood of `u` in `Mˣ` exactly when it contains every unit `v` with `v` in a prescribed
  neighbourhood of `u` and `v⁻¹` in a prescribed neighbourhood of `u⁻¹`.
* In a `T₁` monoid with continuous multiplication, `u ↦ (u, u⁻¹)` is a closed embedding, so the
  units of a σ-compact monoid are σ-compact.
* In a group with zero with continuous inversion away from zero, the coercion `G₀ˣ → G₀` is a
  topological embedding, so a preconnected set of nonzero elements pulls back to a preconnected
  set of units.

## Main results

* `Units.nhds_eq_comap_inf`: the neighbourhood filter of a unit.
* `Units.mem_nhds_iff`: the resulting membership criterion for neighbourhoods of a unit.
* `Units.instSigmaCompactSpace`: the units of a σ-compact monoid are σ-compact.
* `IsPreconnected.preimage_units_val`: preconnected sets of nonzero elements pull back to
  preconnected sets of units.
-/

public section

open Filter Topology

namespace Units

variable {M : Type*} [Monoid M] [TopologicalSpace M]

/-- **The neighbourhood filter of a unit** is the meet of the pullbacks of the neighbourhood
filters of the unit and of its inverse along the two coercions to `M`. -/
theorem nhds_eq_comap_inf (u : Mˣ) :
    𝓝 u = (𝓝 (u : M)).comap val ⊓ (𝓝 (↑u⁻¹ : M)).comap (fun v : Mˣ ↦ (↑v⁻¹ : M)) := by
  have h := @nhds_inf Mˣ (.induced (val : Mˣ → M) ‹_›) (.induced (fun v : Mˣ ↦ (↑v⁻¹ : M)) ‹_›) u
  rwa [nhds_induced, nhds_induced, ← topology_eq_inf] at h

/-- **Neighbourhoods of a unit.**  A set is a neighbourhood of `u` in `Mˣ` exactly when it contains
every unit `v` with `v` in a prescribed neighbourhood of `u` and `v⁻¹` in a prescribed
neighbourhood of `u⁻¹`. -/
theorem mem_nhds_iff {u : Mˣ} {s : Set Mˣ} :
    s ∈ 𝓝 u ↔ ∃ t ∈ 𝓝 (u : M), ∃ t' ∈ 𝓝 (↑u⁻¹ : M),
      ∀ v : Mˣ, (v : M) ∈ t → (↑v⁻¹ : M) ∈ t' → v ∈ s := by
  rw [nhds_eq_comap_inf]
  constructor
  · intro hs
    obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := mem_inf_iff.mp hs
    obtain ⟨t, ht, hts⟩ := mem_comap.mp hs₁
    obtain ⟨t', ht', hts'⟩ := mem_comap.mp hs₂
    exact ⟨t, ht, t', ht', fun v hv hv' ↦ ⟨hts hv, hts' hv'⟩⟩
  · rintro ⟨t, ht, t', ht', h⟩
    exact mem_of_superset (inter_mem (mem_inf_of_left (preimage_mem_comap ht))
      (mem_inf_of_right (preimage_mem_comap ht'))) fun v hv ↦ h v hv.1 hv.2

/-- **The units of a σ-compact monoid are σ-compact.** In a `T₁` monoid with continuous
multiplication, `u ↦ (u, u⁻¹)` is a closed embedding of `Mˣ` into the σ-compact space `M × M`. -/
@[to_additive /-- The additive units of a σ-compact additive monoid are σ-compact. -/]
instance instSigmaCompactSpace [T1Space M] [ContinuousMul M] [SigmaCompactSpace M] :
    SigmaCompactSpace Mˣ :=
  ((Homeomorph.refl M).prodCongr MulOpposite.opHomeomorph.symm).isClosedEmbedding.comp
    isClosedEmbedding_embedProduct |>.sigmaCompactSpace

end Units

/-- **Preconnected sets of nonzero elements pull back to preconnected sets of units.**  In a group
with zero whose inversion is continuous away from zero, the coercion from the units is a
topological embedding, so the units lying over a preconnected set of nonzero elements form a
preconnected set. -/
theorem IsPreconnected.preimage_units_val {G₀ : Type*} [GroupWithZero G₀] [TopologicalSpace G₀]
    [ContinuousInv₀ G₀] {s : Set G₀} (hs : IsPreconnected s) (h0 : 0 ∉ s) :
    IsPreconnected ((Units.val : G₀ˣ → G₀) ⁻¹' s) := by
  have h : s ∩ Set.range (Units.val : G₀ˣ → G₀) = s :=
    Set.inter_eq_left.mpr fun x hx ↦ ⟨Units.mk0 x (ne_of_mem_of_not_mem hx h0), rfl⟩
  rw [← Units.isEmbedding_val₀.isInducing.isPreconnected_image, Set.image_preimage_eq_inter_range,
    h]
  exact hs
