/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Bounds.Defs
public import TauCeti.Topology.Algebra.Group.OpenSubgroup.Basic
import TauCeti.Topology.Algebra.MulAction.Stabilizer

/-!
# Compact open subgroups: directedness, subtype pushforward, and compact open neighbourhoods

In a group `G` with continuous left translations (`ContinuousConstSMul G G`), every open subgroup
`U : OpenSubgroup G` is closed (`OpenSubgroup.isClosed_of_continuousConstSMul`). Consequently:

* an open subgroup contained in a compact set is compact (`OpenSubgroup.isCompact_of_subset`);
* intersecting with a compact open subgroup preserves compactness (`OpenSubgroup.isCompact_inf_left`
  and `OpenSubgroup.isCompact_inf_right`);
* the compact open subgroups of `G` — as well as those contained in a fixed open subgroup `U₀` —
  are directed under reverse inclusion (`OpenSubgroup.directedOn_isCompact`,
  `OpenSubgroup.directedOn_isCompact_le`), and when `U₀` is compact they are coinitial in
  `OpenSubgroup G` (`OpenSubgroup.isCoinitial_isCompact_le`), i.e. cofinal under reverse inclusion;
* a single compact open subgroup makes a topological group locally compact
  (`OpenSubgroup.locallyCompactSpace_of_isCompact`).

Along the subtype pushforward `OpenSubgroup.mapSubtype U V`, compactness in `G` is equivalent to
compactness in `U` (`OpenSubgroup.isCompact_mapSubtype_iff`), and when `U` is compact and `G` has
continuous left translations every `U.mapSubtype V` is compact
(`OpenSubgroup.isCompact_mapSubtype_of_isCompact`).

Finally, in any topological group `G`, every compact open neighbourhood `s` of `1` contains a
compact open subgroup, namely its left translation stabilizer
(`TauCeti.IsTopologicalGroup.exists_openSubgroup_isCompact_subset_of_isCompact_of_isOpen`). This
strengthens Mathlib's `IsTopologicalGroup.exist_openSubgroup_sub_clopen_nhds_of_one`, which assumes
`[CompactSpace G]`, to arbitrary (possibly noncompact) topological groups.

## Main results

* `OpenSubgroup.isCompact_of_subset`, `OpenSubgroup.isCompact_inf_left`,
  `OpenSubgroup.isCompact_inf_right`: compactness of open subgroups inside compact sets and under
  intersections.
* `OpenSubgroup.directedOn_isCompact`, `OpenSubgroup.directedOn_isCompact_le`,
  `OpenSubgroup.isCoinitial_isCompact_le`: directedness and coinitiality of compact open subgroups.
* `OpenSubgroup.locallyCompactSpace_of_isCompact`: local compactness from a compact open subgroup.
* `OpenSubgroup.isCompact_mapSubtype_iff`, `OpenSubgroup.isCompact_mapSubtype`,
  `OpenSubgroup.isCompact_mapSubtype_of_isCompact`: compactness along `OpenSubgroup.mapSubtype`.
* `TauCeti.IsTopologicalGroup.exists_openSubgroup_isCompact_subset_of_isCompact_of_isOpen`, and its
  additive form
  `TauCeti.IsTopologicalAddGroup.exists_openAddSubgroup_isCompact_subset_of_isCompact_of_isOpen`:
  every compact open identity neighbourhood in a topological group contains a compact open subgroup.

## References

* L. Kramer, *Locally Compact Groups and Lie Groups*, Chapter 1 (version of 19 May 2020),
  Lemma 1.41 and Proposition 1.43, pp. 17–18.
-/

public section

open Set

namespace OpenSubgroup

variable {G : Type*} [Group G] [TopologicalSpace G]

section ContinuousConstSMul

variable [ContinuousConstSMul G G]

/-- **An open subgroup contained in a compact set is compact.** Only continuity of left
translations is needed, so that `U` is closed. -/
@[to_additive
/-- **An open additive subgroup contained in a compact set is compact.** Only continuity of left
translations is needed, so that `U` is closed. -/]
theorem isCompact_of_subset (U : OpenSubgroup G) {K : Set G} (hK : IsCompact K)
    (hUK : (U : Set G) ⊆ K) : IsCompact (U : Set G) :=
  hK.of_isClosed_subset U.isClosed_of_continuousConstSMul hUK

/-- Intersecting a compact open subgroup on the right with any open subgroup yields a compact open
subgroup. -/
@[to_additive
/-- Intersecting a compact open additive subgroup on the right with any open additive subgroup
yields a compact open additive subgroup. -/]
theorem isCompact_inf_left {U : OpenSubgroup G} (V : OpenSubgroup G) (hU : IsCompact (U : Set G)) :
    IsCompact ((U ⊓ V : OpenSubgroup G) : Set G) :=
  (U ⊓ V).isCompact_of_subset hU inter_subset_left

/-- Intersecting a compact open subgroup on the left with any open subgroup yields a compact open
subgroup. -/
@[to_additive
/-- Intersecting a compact open additive subgroup on the left with any open additive subgroup yields
a compact open additive subgroup. -/]
theorem isCompact_inf_right {U : OpenSubgroup G} (V : OpenSubgroup G)
    (hU : IsCompact (U : Set G)) : IsCompact ((V ⊓ U : OpenSubgroup G) : Set G) :=
  (V ⊓ U).isCompact_of_subset hU inter_subset_right

/-- **The compact open subgroups are directed under reverse inclusion.** Given two compact open
subgroups `U₁` and `U₂`, their intersection `U₁ ⊓ U₂` is a compact open subgroup contained in both.
-/
@[to_additive
/-- **The compact open additive subgroups are directed under reverse inclusion.** Given two compact
open additive subgroups `U₁` and `U₂`, their intersection `U₁ ⊓ U₂` is a compact open additive
subgroup contained in both. -/]
theorem directedOn_isCompact : DirectedOn (· ≥ ·) {U : OpenSubgroup G | IsCompact (U : Set G)} :=
  fun U₁ hU₁ U₂ _ ↦ ⟨U₁ ⊓ U₂, U₁.isCompact_inf_left U₂ hU₁, inf_le_left, inf_le_right⟩

/-- **The compact open subgroups contained in `U₀` are directed under reverse inclusion.** -/
@[to_additive
/-- **The compact open additive subgroups contained in `U₀` are directed under reverse
inclusion.** -/]
theorem directedOn_isCompact_le (U₀ : OpenSubgroup G) :
    DirectedOn (· ≥ ·) {U : OpenSubgroup G | IsCompact (U : Set G) ∧ U ≤ U₀} :=
  fun U₁ hU₁ U₂ _ ↦
    ⟨U₁ ⊓ U₂, ⟨U₁.isCompact_inf_left U₂ hU₁.1, inf_le_of_left_le hU₁.2⟩, inf_le_left, inf_le_right⟩

/-- **The compact open subgroups contained in a compact open subgroup `U₀` are coinitial in
`OpenSubgroup G`** (cofinal under reverse inclusion): every open subgroup `V` contains the compact
open subgroup `V ⊓ U₀ ≤ U₀`. -/
@[to_additive
/-- **The compact open additive subgroups contained in a compact open additive subgroup `U₀` are
coinitial in `OpenAddSubgroup G`** (cofinal under reverse inclusion): every open additive subgroup
`V` contains the compact open additive subgroup `V ⊓ U₀ ≤ U₀`. -/]
theorem isCoinitial_isCompact_le {U₀ : OpenSubgroup G} (hU₀ : IsCompact (U₀ : Set G)) :
    IsCoinitial {U : OpenSubgroup G | IsCompact (U : Set G) ∧ U ≤ U₀} :=
  fun V ↦ ⟨V ⊓ U₀, ⟨U₀.isCompact_inf_right V hU₀, inf_le_right⟩, inf_le_left⟩

end ContinuousConstSMul

/-- A topological group possessing a compact open subgroup is locally compact, since that subgroup
is a compact neighbourhood of `1`. -/
@[to_additive
/-- A topological additive group possessing a compact open additive subgroup is locally compact,
since that subgroup is a compact neighbourhood of `0`. -/]
theorem locallyCompactSpace_of_isCompact [IsTopologicalGroup G] {U : OpenSubgroup G}
    (hU : IsCompact (U : Set G)) : LocallyCompactSpace G :=
  hU.locallyCompactSpace_of_mem_nhds_of_group U.mem_nhds_one

section MapSubtype

/-- `U.mapSubtype V` is compact in `G` if and only if `V` is compact in `U`. -/
-- Not `@[simp]`: `OpenSubgroup.coe_mapSubtype` simplifies the left-hand side to
-- `IsCompact (Subtype.val '' ↑V)`, so `simpNF` rejects the attribute.
@[to_additive
/-- `U.mapSubtype V` is compact in `G` if and only if `V` is compact in `U`. -/]
theorem isCompact_mapSubtype_iff {U : OpenSubgroup G} {V : OpenSubgroup U} :
    IsCompact ((U.mapSubtype V : OpenSubgroup G) : Set G) ↔ IsCompact (V : Set U) := by
  rw [coe_mapSubtype, ← Subtype.isCompact_iff]

/-- Pushing forward a compact open subgroup of `U` gives a compact open subgroup of `G`. -/
@[to_additive
/-- Pushing forward a compact open additive subgroup of `U` gives a compact open additive subgroup
of `G`. -/]
theorem isCompact_mapSubtype {U : OpenSubgroup G} {V : OpenSubgroup U}
    (hV : IsCompact (V : Set U)) : IsCompact ((U.mapSubtype V : OpenSubgroup G) : Set G) :=
  isCompact_mapSubtype_iff.mpr hV

/-- Every open subgroup `V` of a compact open subgroup `U` pushes forward to a compact open
subgroup of `G`, provided `G` has continuous left translations. -/
@[to_additive
/-- Every open additive subgroup `V` of a compact open additive subgroup `U` pushes forward to a
compact open additive subgroup of `G`, provided `G` has continuous left translations. -/]
theorem isCompact_mapSubtype_of_isCompact [ContinuousConstSMul G G] {U : OpenSubgroup G}
    (hU : IsCompact (U : Set G)) (V : OpenSubgroup U) :
    IsCompact ((U.mapSubtype V : OpenSubgroup G) : Set G) :=
  (U.mapSubtype V).isCompact_of_subset hU (U.mapSubtype_le V)

end MapSubtype

end OpenSubgroup

namespace TauCeti

open scoped Pointwise in
/-- **Every compact open identity neighbourhood contains a compact open subgroup.** Given a compact
open subset `s` of a topological group `G` with `1 ∈ s`, its left translation stabilizer
`MulAction.stabilizer G s` is a compact open subgroup contained in `s`. -/
@[to_additive
IsTopologicalAddGroup.exists_openAddSubgroup_isCompact_subset_of_isCompact_of_isOpen
/-- **Every compact open neighbourhood of zero contains a compact open additive subgroup.** Given a
compact open subset `s` of a topological additive group `G` with `0 ∈ s`, its translation
stabilizer `AddAction.stabilizer G s` is a compact open additive subgroup contained in `s`. -/]
theorem IsTopologicalGroup.exists_openSubgroup_isCompact_subset_of_isCompact_of_isOpen
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {s : Set G}
    (hs : IsCompact s) (hso : IsOpen s) (h1 : (1 : G) ∈ s) :
    ∃ H : OpenSubgroup G, IsCompact (H : Set G) ∧ (H : Set G) ⊆ s :=
  ⟨⟨_root_.MulAction.stabilizer G s, MulAction.isOpen_stabilizer_of_isCompact_of_isOpen hs hso⟩,
    MulAction.isCompact_stabilizer_of_isCompact_of_isOpen ⟨1, h1⟩ hs hso,
    fun g hg ↦ by simpa only [smul_eq_mul, mul_one] using
      (_root_.MulAction.mem_stabilizer_set.mp hg 1).mpr h1⟩

end TauCeti
