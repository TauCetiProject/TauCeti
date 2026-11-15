/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Topology of open subgroups and their coset spaces

An open subgroup `U : OpenSubgroup G` carries a `Group` structure through `SubgroupClass` and the
subspace topology through `SetLike.coe`, but instance search does not unfold `↥U` to
`↥U.toSubgroup`. Consequently Mathlib's `Subgroup` instances for topological groups do not fire
directly on `U : OpenSubgroup G`, nor does the open-subset theorem `IsOpen.locallyCompactSpace`.

This file registers those instances directly on `OpenSubgroup G` (and `OpenAddSubgroup G`):
separate and joint continuity of multiplication, continuity of inversion, `IsTopologicalGroup`,
`LocallyCompactSpace` (using openness alone), and `WeaklyLocallyCompactSpace` and `CompactSpace`
(using that an open subgroup of a topological group with separately continuous multiplication is
also closed).

The continuity criteria `OpenSubgroup.continuous_mk_inf_iff` and
`OpenSubgroup.continuous_mk_comap_iff` describe maps into coset spaces of intersections and
preimages. These apply to arbitrary open subgroups, without normality. Separate continuity of
multiplication makes the target coset spaces discrete; the preimage criterion only needs this
on the target group of the homomorphism.

## Main instances

* `OpenSubgroup.instSeparatelyContinuousMul`, `OpenSubgroup.instContinuousMul`,
  `OpenSubgroup.instContinuousInv`, `OpenSubgroup.instIsTopologicalGroup`: topological group
  operations on an open subgroup, with additive versions on `OpenAddSubgroup`.
* `OpenSubgroup.instLocallyCompactSpace`, `OpenSubgroup.instWeaklyLocallyCompactSpace`,
  `OpenSubgroup.instCompactSpace`: local compactness and compactness inherited from the ambient
  group, with additive versions on `OpenAddSubgroup`.
* `Subgroup.isCompact_of_isOpen_of_subset`, `OpenSubgroup.isCompact_of_subset`,
  `OpenSubgroup.isCompact_of_le`, `OpenSubgroup.isCompact_inf_left`,
  `OpenSubgroup.isCompact_inf_right`, and `OpenSubgroup.directedOn_isCompact_le`: compactness of
  open subgroups contained in compact sets, preservation under intersection, and
  downward-directedness below a fixed open subgroup.
* `OpenSubgroup.instUniqueOfSubsingleton`, `OpenSubgroup.isCompact_top_of_subsingleton`, and
  `OpenSubgroup.nhds_one_hasBasis_eq_top`: a subsingleton topological group has `{⊤}` as its
  singleton compact open subgroup basis.
-/

public section

open Filter
open scoped Topology

/-- An open subgroup contained in a compact subset of a group with separately continuous
multiplication is compact. -/
@[to_additive /-- An open additive subgroup contained in a compact subset of an additive group with
separately continuous addition is compact. -/]
theorem Subgroup.isCompact_of_isOpen_of_subset {G : Type*} [Group G] [TopologicalSpace G]
    [SeparatelyContinuousMul G] {H : Subgroup G} {K : Set G} (hHo : IsOpen (H : Set G))
    (hK : IsCompact K) (hHK : (H : Set G) ⊆ K) : IsCompact (H : Set G) :=
  hK.of_isClosed_subset (H.isClosed_of_isOpen hHo) hHK

namespace OpenSubgroup

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- An open subgroup of a group with separately continuous multiplication has separately
continuous multiplication. -/
@[to_additive /-- An open additive subgroup of an additive group with separately continuous
addition has separately continuous addition. -/]
instance instSeparatelyContinuousMul [SeparatelyContinuousMul G] (U : OpenSubgroup G) :
    SeparatelyContinuousMul U :=
  U.toSubgroup.toSubmonoid.separatelyContinuousMul

/-- An open subgroup of a group with continuous multiplication has continuous multiplication. -/
@[to_additive /-- An open additive subgroup of an additive group with continuous addition has
continuous addition. -/]
instance instContinuousMul [ContinuousMul G] (U : OpenSubgroup G) : ContinuousMul U :=
  U.toSubgroup.toSubmonoid.continuousMul

/-- An open subgroup of a group with continuous inversion has continuous inversion. -/
@[to_additive /-- An open additive subgroup of an additive group with continuous negation has
continuous negation. -/]
instance instContinuousInv [ContinuousInv G] (U : OpenSubgroup G) : ContinuousInv U :=
  ⟨continuous_inv.subtype_map fun _ hx ↦ inv_mem hx⟩

/-- An open subgroup of a topological group is a topological group. -/
@[to_additive /-- An open additive subgroup of a topological additive group is a topological
additive group. -/]
instance instIsTopologicalGroup [IsTopologicalGroup G] (U : OpenSubgroup G) :
    IsTopologicalGroup U where

/-- An open subgroup of a locally compact group is locally compact. -/
@[to_additive /-- An open additive subgroup of a locally compact additive group is locally
compact. -/]
instance instLocallyCompactSpace [LocallyCompactSpace G] (U : OpenSubgroup G) :
    LocallyCompactSpace U :=
  U.isOpen.locallyCompactSpace

/-- An open subgroup of a weakly locally compact group with separately continuous multiplication is
weakly locally compact, since it is closed. -/
@[to_additive /-- An open additive subgroup of a weakly locally compact additive group with
separately continuous addition is weakly locally compact, since it is closed. -/]
instance instWeaklyLocallyCompactSpace [SeparatelyContinuousMul G] [WeaklyLocallyCompactSpace G]
    (U : OpenSubgroup G) : WeaklyLocallyCompactSpace U :=
  U.isClosed.weaklyLocallyCompactSpace

/-- An open subgroup of a compact group with separately continuous multiplication is compact, since
it is closed. -/
@[to_additive /-- An open additive subgroup of a compact additive group with separately continuous
addition is compact, since it is closed. -/]
instance instCompactSpace [SeparatelyContinuousMul G] [CompactSpace G] (U : OpenSubgroup G) :
    CompactSpace U :=
  isCompact_iff_compactSpace.mp U.isClosed.isCompact

/-- An open subgroup contained in a compact set (in particular, in a compact neighbourhood of `1`)
is compact. -/
@[to_additive /-- An open additive subgroup contained in a compact set (in particular, in a compact
neighbourhood of `0`) is compact. -/]
theorem isCompact_of_subset [SeparatelyContinuousMul G] (U : OpenSubgroup G) {K : Set G}
    (hK : IsCompact K) (hUK : (U : Set G) ⊆ K) : IsCompact (U : Set G) :=
  U.toSubgroup.isCompact_of_isOpen_of_subset U.isOpen hK hUK

/-- An open subgroup contained in a compact open subgroup is compact. -/
@[to_additive /-- An open additive subgroup contained in a compact open additive subgroup is
compact. -/]
theorem isCompact_of_le [SeparatelyContinuousMul G] {U V : OpenSubgroup G} (hUV : U ≤ V)
    (hV : IsCompact (V : Set G)) : IsCompact (U : Set G) :=
  U.isCompact_of_subset hV hUV

/-- The intersection of two open subgroups is compact when the left factor is compact. -/
@[to_additive /-- The intersection of two open additive subgroups is compact when the left factor
is compact. -/]
theorem isCompact_inf_left [SeparatelyContinuousMul G] {U V : OpenSubgroup G}
    (hU : IsCompact (U : Set G)) : IsCompact ((U ⊓ V : OpenSubgroup G) : Set G) :=
  isCompact_of_le inf_le_left hU

/-- The intersection of two open subgroups is compact when the right factor is compact. -/
@[to_additive /-- The intersection of two open additive subgroups is compact when the right factor
is compact. -/]
theorem isCompact_inf_right [SeparatelyContinuousMul G] {U V : OpenSubgroup G}
    (hV : IsCompact (V : Set G)) : IsCompact ((U ⊓ V : OpenSubgroup G) : Set G) :=
  isCompact_of_le inf_le_right hV

/-- The compact open subgroups contained in a fixed open subgroup `U₀` form a downward-directed
family (that is, a directed family under reverse inclusion `≥`). -/
@[to_additive /-- The compact open additive subgroups contained in a fixed open additive subgroup
`U₀` form a downward-directed family (that is, a directed family under reverse inclusion `≥`). -/]
theorem directedOn_isCompact_le [SeparatelyContinuousMul G] (U₀ : OpenSubgroup G) :
    DirectedOn (· ≥ ·) {K : OpenSubgroup G | IsCompact (K : Set G) ∧ K ≤ U₀} :=
  fun _ hK₁ _ _ ↦
    ⟨_, ⟨isCompact_inf_left hK₁.1, inf_le_of_left_le hK₁.2⟩, inf_le_left, inf_le_right⟩

/-- In a subsingleton topological group, `⊤` is the unique open subgroup. -/
@[to_additive /-- In a subsingleton topological additive group, `⊤` is the unique open additive
subgroup. -/]
instance instUniqueOfSubsingleton [Subsingleton G] : Unique (OpenSubgroup G) where
  default := ⊤
  uniq U := SetLike.ext fun x ↦ by
    simp [Subsingleton.elim x 1]

/-- The unique open subgroup `⊤` of a subsingleton topological group is compact. -/
@[to_additive /-- The unique open additive subgroup `⊤` of a subsingleton topological additive
group is compact. -/]
theorem isCompact_top_of_subsingleton [Subsingleton G] :
    IsCompact ((⊤ : OpenSubgroup G) : Set G) :=
  Set.Subsingleton.isCompact Set.subsingleton_of_subsingleton

variable (G) in
/-- A subsingleton topological group has the singleton `{⊤}` as an open-subgroup basis of `𝓝 1`
(compact by `OpenSubgroup.isCompact_top_of_subsingleton`). -/
@[to_additive /-- A subsingleton topological additive group has the singleton `{⊤}` as an
open-additive-subgroup basis of `𝓝 0` (compact by
`OpenAddSubgroup.isCompact_top_of_subsingleton`). -/]
theorem nhds_one_hasBasis_eq_top [Subsingleton G] :
    (𝓝 (1 : G)).HasBasis (fun K : OpenSubgroup G ↦ K = ⊤) fun K ↦ (K : Set G) :=
  ⟨fun U ↦ ⟨fun hU ↦
      ⟨⊤, rfl, fun x _ ↦ by simpa [Subsingleton.elim x 1] using mem_of_mem_nhds hU⟩,
    fun ⟨K, _, hKU⟩ ↦ mem_of_superset K.mem_nhds_one hKU⟩⟩

variable {H X : Type*} [Group H] [TopologicalSpace H] [TopologicalSpace X]

/-- A map into the coset space of an intersection of open subgroups is continuous if and only
if its projections to both coset spaces are continuous. Normality is not required. -/
theorem continuous_mk_inf_iff [SeparatelyContinuousMul G] {U V : OpenSubgroup G} {g : X → G} :
    (Continuous fun x ↦ (g x : G ⧸ (U ⊓ V).toSubgroup)) ↔
      (Continuous fun x ↦ (g x : G ⧸ U.toSubgroup)) ∧
      (Continuous fun x ↦ (g x : G ⧸ V.toSubgroup)) := by
  constructor
  · intro h
    have hU : Continuous (Subgroup.quotientMapOfLE
        (inf_le_left : U.toSubgroup ⊓ V.toSubgroup ≤ U.toSubgroup)) :=
      (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr QuotientGroup.continuous_mk
    have hV : Continuous (Subgroup.quotientMapOfLE
        (inf_le_right : U.toSubgroup ⊓ V.toSubgroup ≤ V.toSubgroup)) :=
      (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr QuotientGroup.continuous_mk
    exact ⟨hU.comp h, hV.comp h⟩
  · rintro ⟨hU, hV⟩
    apply IsLocallyConstant.continuous
    rw [IsLocallyConstant.iff_isOpen_fiber_apply]
    intro x
    have hfiber :
        (fun y ↦ (g y : G ⧸ (U ⊓ V).toSubgroup)) ⁻¹' {(g x : G ⧸ (U ⊓ V).toSubgroup)} =
          (fun y ↦ (g y : G ⧸ U.toSubgroup)) ⁻¹' {(g x : G ⧸ U.toSubgroup)} ∩
          (fun y ↦ (g y : G ⧸ V.toSubgroup)) ⁻¹' {(g x : G ⧸ V.toSubgroup)} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, QuotientGroup.eq]
      exact Subgroup.mem_inf
    rw [hfiber]
    exact (hU.isOpen_preimage _ (isOpen_discrete _)).inter
      (hV.isOpen_preimage _ (isOpen_discrete _))

/-- A map into the coset space of the preimage of an open subgroup is continuous if and only
if its composite with the homomorphism and the target coset projection is continuous.
Normality and continuity of the group operations on the source are not required. -/
theorem continuous_mk_comap_iff [SeparatelyContinuousMul H] (U : OpenSubgroup H) (f : G →* H)
    (hf : Continuous f) {g : X → G} :
    (Continuous fun x ↦ (g x : G ⧸ (U.comap f hf).toSubgroup)) ↔
      (Continuous fun x ↦ (f (g x) : H ⧸ U.toSubgroup)) := by
  let φ : G ⧸ (U.comap f hf).toSubgroup → H ⧸ U.toSubgroup :=
    Quotient.map' f fun a b h ↦ by
      simpa only [QuotientGroup.leftRel_apply, toSubgroup_comap, Subgroup.mem_comap,
        map_mul, map_inv] using h
  constructor
  · intro h
    have hφ : Continuous φ :=
      (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
        (QuotientGroup.continuous_mk.comp hf)
    exact hφ.comp h
  · intro h
    apply IsLocallyConstant.continuous
    rw [IsLocallyConstant.iff_isOpen_fiber_apply]
    intro x
    have hfiber :
        (fun y ↦ (g y : G ⧸ (U.comap f hf).toSubgroup)) ⁻¹'
          {(g x : G ⧸ (U.comap f hf).toSubgroup)} =
        (fun y ↦ (f (g y) : H ⧸ U.toSubgroup)) ⁻¹' {(f (g x) : H ⧸ U.toSubgroup)} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff, QuotientGroup.eq]
      simp only [toSubgroup_comap, Subgroup.mem_comap, map_mul, map_inv]
    rw [hfiber]
    exact h.isOpen_preimage _ (isOpen_discrete _)

end OpenSubgroup
