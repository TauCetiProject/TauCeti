/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Connected.PathConnected

/-!
# Separation, neighbourhoods, σ-compactness and connectedness in a group of units

The units `Mˣ` of a topological monoid `M` carry the topology induced by `u ↦ (u, u⁻¹)`.  This
file records consequences of that definition.

* The units of a `T₁` monoid form a `T₁` space, without a continuity assumption on multiplication.
* The neighbourhood filter of a unit `u` is the meet of the pullbacks of the neighbourhood filters
  of `u` and of `u⁻¹` along the coercion and the inverse coercion.  Concretely, a set is a
  neighbourhood of `u` in `Mˣ` exactly when it contains every unit `v` with `v` in a prescribed
  neighbourhood of `u` and `v⁻¹` in a prescribed neighbourhood of `u⁻¹`.
* In a `T₁` monoid with continuous multiplication, `u ↦ (u, u⁻¹)` is a closed embedding, so the
  units of a σ-compact monoid are σ-compact.
* In a group with zero with continuous inversion away from zero, the coercion `G₀ˣ → G₀` is a
  topological embedding, so a preconnected set of nonzero elements pulls back to a preconnected
  set of units.
* Whenever `Units.val : Mˣ → M` is a topological embedding onto `{m : M | IsUnit m}`, the set of
  units is path-connected if and only if the topological group `Mˣ` is.

## Main results

* `Units.instT1Space`: the `T₁` separation property for units.
* `Units.nhds_eq_comap_inf`: the neighbourhood filter of a unit.
* `Units.mem_nhds_iff`: the resulting membership criterion for neighbourhoods of a unit.
* `Units.instSigmaCompactSpace`: the units of a σ-compact monoid are σ-compact.
* `IsPreconnected.preimage_units_val`: preconnected sets of nonzero elements pull back to
  preconnected sets of units.
* `Topology.IsEmbedding.isPathConnected_isUnit_iff`: when `Units.val : Mˣ → M` is an embedding,
  `{m : M | IsUnit m}` is path-connected if and only if `Mˣ` is.
-/

public section

open Filter Topology

namespace Units

variable {M : Type*} [Monoid M] [TopologicalSpace M]

/-- The units of a `T₁` monoid form a `T₁` space. -/
@[to_additive /-- The additive units of a `T₁` additive monoid form a `T₁` space. -/]
instance instT1Space [T1Space M] : T1Space Mˣ :=
  t1Space_of_injective_of_continuous val_injective continuous_val

/-- **The neighbourhood filter of a unit** is the meet of the pullbacks of the neighbourhood
filters of the unit and of its inverse along the two coercions to `M`. -/
@[to_additive /-- **The neighbourhood filter of an additive unit** is the meet of the pullbacks of
the neighbourhood filters of the additive unit and of its negation along the two coercions to
`M`. -/]
theorem nhds_eq_comap_inf (u : Mˣ) :
    𝓝 u = (𝓝 (u : M)).comap val ⊓ (𝓝 (↑u⁻¹ : M)).comap (fun v : Mˣ ↦ (↑v⁻¹ : M)) := by
  have h := @nhds_inf Mˣ (.induced (val : Mˣ → M) ‹_›) (.induced (fun v : Mˣ ↦ (↑v⁻¹ : M)) ‹_›) u
  rwa [nhds_induced, nhds_induced, ← topology_eq_inf] at h

/-- **Neighbourhoods of a unit.**  A set is a neighbourhood of `u` in `Mˣ` exactly when it contains
every unit `v` with `v` in a prescribed neighbourhood of `u` and `v⁻¹` in a prescribed
neighbourhood of `u⁻¹`. -/
@[to_additive /-- **Neighbourhoods of an additive unit.**  A set is a neighbourhood of `u` in
`AddUnits M` exactly when it contains every additive unit `v` with `v` in a prescribed
neighbourhood of `u` and `-v` in a prescribed neighbourhood of `-u`. -/]
theorem mem_nhds_iff {u : Mˣ} {s : Set Mˣ} :
    s ∈ 𝓝 u ↔ ∃ t ∈ 𝓝 (u : M), ∃ t' ∈ 𝓝 (↑u⁻¹ : M),
      ∀ v : Mˣ, (v : M) ∈ t → (↑v⁻¹ : M) ∈ t' → v ∈ s := by
  simp only [nhds_eq_comap_inf, mem_inf_iff_superset, mem_comap]
  constructor
  · rintro ⟨_, ⟨t, ht, hts⟩, _, ⟨t', ht', hts'⟩, h⟩
    exact ⟨t, ht, t', ht', fun v hv hv' ↦ h ⟨hts hv, hts' hv'⟩⟩
  · rintro ⟨t, ht, t', ht', h⟩
    exact ⟨_, ⟨t, ht, subset_rfl⟩, _, ⟨t', ht', subset_rfl⟩, fun v hv ↦ h v hv.1 hv.2⟩

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
  rwa [← Units.isEmbedding_val₀.isInducing.isPreconnected_image, Set.image_preimage_eq_of_subset
    fun x hx ↦ ⟨Units.mk0 x (ne_of_mem_of_not_mem hx h0), rfl⟩]

namespace Topology

/-- In a topological monoid `M` whose unit inclusion `Units.val : Mˣ → M` is an embedding (for
example, a normed ring with summable geometric series or a topological monoid with open units), the
set `{m : M | IsUnit m}` of invertible elements is path-connected if and only if the topological
group `Mˣ` is path-connected. -/
theorem IsEmbedding.isPathConnected_isUnit_iff {M : Type*} [Monoid M] [TopologicalSpace M]
    (h : IsEmbedding (Units.val : Mˣ → M)) :
    IsPathConnected {m : M | IsUnit m} ↔ PathConnectedSpace Mˣ := by
  have hrange : (Units.val : Mˣ → M) '' Set.univ = {m : M | IsUnit m} := by
    ext m
    exact ⟨fun ⟨u, _, hu⟩ ↦ hu ▸ u.isUnit, fun hm ↦ ⟨hm.unit, Set.mem_univ _, hm.unit_spec⟩⟩
  rw [← hrange, ← h.isInducing.isPathConnected_iff, pathConnectedSpace_iff_univ]

end Topology
