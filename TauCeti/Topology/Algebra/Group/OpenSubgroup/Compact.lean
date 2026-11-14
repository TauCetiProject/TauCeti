/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Bounds.Defs
public import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Group.Pointwise

/-!
# Compact open subgroups: closedness, directedness, and subtype pushforward

In a group `G` with continuous left translations (`ContinuousConstSMul G G`), every open subgroup
`U : OpenSubgroup G` is closed, being the complement of the union of its nontrivial left cosets.
This weakens Mathlib's `OpenSubgroup.isClosed`, which assumes `[SeparatelyContinuousMul G]`.
Consequently:

* an open subgroup contained in a compact set is compact (`OpenSubgroup.isCompact_of_subset`);
* intersecting with a compact open subgroup preserves compactness (`OpenSubgroup.isCompact_inf_left`
  and `OpenSubgroup.isCompact_inf_right`);
* the compact open subgroups of `G` — as well as those contained in a fixed open subgroup `U₀` —
  are directed under reverse inclusion (`OpenSubgroup.directedOn_isCompact`,
  `OpenSubgroup.directedOn_isCompact_le`), and when `U₀` is compact they are coinitial in
  `OpenSubgroup G` (`OpenSubgroup.isCoinitial_isCompact_le`), i.e. cofinal under reverse inclusion;
* a single compact open subgroup makes a topological group locally compact
  (`OpenSubgroup.locallyCompactSpace_of_isCompact`).

Finally, for any group with a topology, `OpenSubgroup.mapSubtype U V` pushes an open subgroup `V`
of `U : OpenSubgroup G` forward along `U.toSubgroup.subtype : U →* G` to an open subgroup of `G`
contained in `U`, inverse to pullback on `{W : OpenSubgroup G | W ≤ U}`. When `U` is compact and
`G` has continuous left translations, every `U.mapSubtype V` is compact.

## Main definitions and results

* `OpenSubgroup.isClosed_of_continuousConstSMul`, `OpenSubgroup.isCompact_of_subset`: closedness
  and compactness inside a compact set under `[ContinuousConstSMul G G]`.
* `OpenSubgroup.directedOn_isCompact`, `OpenSubgroup.directedOn_isCompact_le`,
  `OpenSubgroup.isCoinitial_isCompact_le`: directedness and coinitiality of compact open subgroups.
* `OpenSubgroup.compactSpace_of_isCompact`, `OpenSubgroup.locallyCompactSpace_of_isCompact`.
* `OpenSubgroup.mapSubtype`: pushforward of an open subgroup of an open subgroup to the ambient
  group, with its characteristic `simp` API and compactness transfer.

## References

* L. Kramer, *Locally Compact Groups and Lie Groups*, Chapter 1 (version of 19 May 2020),
  Proposition 1.43, p. 18.
-/

public section

open Set
open scoped Pointwise

namespace OpenSubgroup

variable {G : Type*} [Group G] [TopologicalSpace G]

section ContinuousConstSMul

variable [ContinuousConstSMul G G]

/-- **An open subgroup of a group with continuous left translations is closed.** Its complement is
the union of its nontrivial left cosets `g • U` for `g ∉ U`. This weakens `OpenSubgroup.isClosed`,
which assumes `[SeparatelyContinuousMul G]`. -/
@[to_additive
/-- **An open additive subgroup of an additive group with continuous left translations is closed.**
Its complement is the union of its nontrivial left cosets `g +ᵥ U` for `g ∉ U`. This weakens
`OpenAddSubgroup.isClosed`, which assumes `[SeparatelyContinuousAdd G]`. -/]
theorem isClosed_of_continuousConstSMul (U : OpenSubgroup G) : IsClosed (U : Set G) := by
  rw [← isOpen_compl_iff]
  have hcompl : (U : Set G)ᶜ = ⋃ (g : G) (_ : g ∉ U), g • (U : Set G) := by
    ext x
    simp only [mem_compl_iff, SetLike.mem_coe, mem_iUnion, mem_smul_set, smul_eq_mul]
    refine ⟨fun hx ↦ ⟨x, hx, 1, U.one_mem, mul_one x⟩, ?_⟩
    rintro ⟨g, hg, u, hu, rfl⟩ hgu
    exact hg (by simpa only [mul_inv_cancel_right] using mul_mem hgu (inv_mem hu))
  rw [hcompl]
  exact isOpen_iUnion fun (g : G) ↦ isOpen_iUnion fun (_ : g ∉ U) ↦ by
    simpa only [image_smul] using isOpenMap_smul g _ U.isOpen

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

/-- Reinterpret `IsCompact (U : Set G)` as `CompactSpace U` on the subtype of `U : OpenSubgroup G`.
-/
@[to_additive
/-- Reinterpret `IsCompact (U : Set G)` as `CompactSpace U` on the subtype of
`U : OpenAddSubgroup G`. -/]
theorem compactSpace_of_isCompact {U : OpenSubgroup G} (hU : IsCompact (U : Set G)) :
    CompactSpace U :=
  isCompact_iff_compactSpace.mp hU

/-- A topological group possessing a compact open subgroup is locally compact, since that subgroup
is a compact neighbourhood of `1`. -/
@[to_additive
/-- A topological additive group possessing a compact open additive subgroup is locally compact,
since that subgroup is a compact neighbourhood of `0`. -/]
theorem locallyCompactSpace_of_isCompact [IsTopologicalGroup G] {U : OpenSubgroup G}
    (hU : IsCompact (U : Set G)) : LocallyCompactSpace G :=
  hU.locallyCompactSpace_of_mem_nhds_of_group U.mem_nhds_one

section MapSubtype

/-- **Pushforward of an open subgroup along an open subgroup's inclusion.** An open subgroup `V` of
`U : OpenSubgroup G` is open in `U`, and `U` is open in `G`, so the image of `V` in `G` is an open
subgroup of `G` contained in `U`. No continuity of the group operations is required. -/
@[to_additive
/-- **Pushforward of an open additive subgroup along an open additive subgroup's inclusion.** An
open additive subgroup `V` of `U : OpenAddSubgroup G` is open in `U`, and `U` is open in `G`, so
the image of `V` in `G` is an open additive subgroup of `G` contained in `U`. No continuity of the
group operations is required. -/]
def mapSubtype (U : OpenSubgroup G) (V : OpenSubgroup U) : OpenSubgroup G :=
  ⟨V.toSubgroup.map U.toSubgroup.subtype, U.isOpen.isOpenMap_subtype_val _ V.isOpen⟩

/-- The underlying subgroup of `U.mapSubtype V` is `V.toSubgroup.map U.toSubgroup.subtype`. -/
@[to_additive (attr := simp, norm_cast)
/-- The underlying additive subgroup of `U.mapSubtype V` is
`V.toAddSubgroup.map U.toAddSubgroup.subtype`. -/]
theorem toSubgroup_mapSubtype (U : OpenSubgroup G) (V : OpenSubgroup U) :
    (U.mapSubtype V : Subgroup G) = V.toSubgroup.map U.toSubgroup.subtype :=
  (rfl)

/-- As a set in `G`, `U.mapSubtype V` is the image of `(V : Set U)` under `Subtype.val`. -/
@[to_additive (attr := simp, norm_cast)
/-- As a set in `G`, `U.mapSubtype V` is the image of `(V : Set U)` under `Subtype.val`. -/]
theorem coe_mapSubtype (U : OpenSubgroup G) (V : OpenSubgroup U) :
    ((U.mapSubtype V : OpenSubgroup G) : Set G) = Subtype.val '' (V : Set U) :=
  Subgroup.coe_map U.toSubgroup.subtype V.toSubgroup

/-- An element `g : G` belongs to `U.mapSubtype V` iff `g ∈ U` and `⟨g, ‹_›⟩ ∈ V`. -/
@[to_additive (attr := simp)
/-- An element `g : G` belongs to `U.mapSubtype V` iff `g ∈ U` and `⟨g, ‹_›⟩ ∈ V`. -/]
theorem mem_mapSubtype_iff {U : OpenSubgroup G} {V : OpenSubgroup U} {g : G} :
    g ∈ U.mapSubtype V ↔ ∃ h : g ∈ U, (⟨g, h⟩ : U) ∈ V := by
  rw [← SetLike.mem_coe, coe_mapSubtype]
  exact ⟨fun ⟨⟨x, hx⟩, hxV, hxeq⟩ ↦ hxeq ▸ ⟨hx, hxV⟩, fun ⟨h, hgV⟩ ↦ ⟨⟨g, h⟩, hgV, rfl⟩⟩

/-- `U.mapSubtype V` is contained in `U`. -/
@[to_additive /-- `U.mapSubtype V` is contained in `U`. -/]
theorem mapSubtype_le (U : OpenSubgroup G) (V : OpenSubgroup U) : U.mapSubtype V ≤ U :=
  fun _ hg ↦ (mem_mapSubtype_iff.mp hg).1

/-- Pulling `U.mapSubtype V` back along `U.toSubgroup.subtype` recovers `V`. -/
@[to_additive (attr := simp)
/-- Pulling `U.mapSubtype V` back along `U.toAddSubgroup.subtype` recovers `V`. -/]
theorem comap_subtype_mapSubtype (U : OpenSubgroup G) (V : OpenSubgroup U) :
    (U.mapSubtype V).comap U.toSubgroup.subtype continuous_subtype_val = V := by
  ext ⟨g, hg⟩
  exact mem_mapSubtype_iff.trans ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨hg, h⟩⟩

/-- Pushing forward the pullback of an open subgroup `W ≤ U` recovers `W`. -/
@[to_additive (attr := simp)
/-- Pushing forward the pullback of an open additive subgroup `W ≤ U` recovers `W`. -/]
theorem mapSubtype_comap_subtype {U W : OpenSubgroup G} (hWU : W ≤ U) :
    U.mapSubtype (W.comap U.toSubgroup.subtype continuous_subtype_val) = W := by
  ext g
  exact mem_mapSubtype_iff.trans ⟨fun ⟨_, hgW⟩ ↦ hgW, fun hgW ↦ ⟨hWU hgW, hgW⟩⟩

/-- `U.mapSubtype` is injective. -/
@[to_additive /-- `U.mapSubtype` is injective. -/]
theorem mapSubtype_injective (U : OpenSubgroup G) : Function.Injective U.mapSubtype :=
  Function.LeftInverse.injective U.comap_subtype_mapSubtype

/-- `U.mapSubtype` reflects and preserves inclusion. -/
@[to_additive (attr := simp) /-- `U.mapSubtype` reflects and preserves inclusion. -/]
theorem mapSubtype_le_mapSubtype_iff {U : OpenSubgroup G} {V₁ V₂ : OpenSubgroup U} :
    U.mapSubtype V₁ ≤ U.mapSubtype V₂ ↔ V₁ ≤ V₂ := by
  refine ⟨fun h x hx ↦ ?_, fun h g hg ↦ ?_⟩
  · have hx' : (x : G) ∈ U.mapSubtype V₂ := h (mem_mapSubtype_iff.mpr ⟨x.2, hx⟩)
    exact (mem_mapSubtype_iff.mp hx').2
  · obtain ⟨hgU, hgV₁⟩ := mem_mapSubtype_iff.mp hg
    exact mem_mapSubtype_iff.mpr ⟨hgU, h hgV₁⟩

/-- Pushing forward a compact open subgroup of `U` gives a compact open subgroup of `G`. -/
@[to_additive
/-- Pushing forward a compact open additive subgroup of `U` gives a compact open additive subgroup
of `G`. -/]
theorem isCompact_mapSubtype {U : OpenSubgroup G} {V : OpenSubgroup U}
    (hV : IsCompact (V : Set U)) : IsCompact ((U.mapSubtype V : OpenSubgroup G) : Set G) := by
  rw [coe_mapSubtype]
  exact hV.image continuous_subtype_val

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
