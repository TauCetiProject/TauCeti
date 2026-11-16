/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Pointwise.Stabilizer
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Separation.Regular
public import TauCeti.Topology.Algebra.Group.OpenSubgroup.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
import TauCeti.Topology.Algebra.Group.Pointwise

/-!
# Van Dantzig's theorem and locally profinite groups

A Hausdorff topological group is *locally profinite* when every neighbourhood of the identity
contains a compact open subgroup. Van Dantzig's theorem identifies these groups with the locally
compact totally disconnected Hausdorff topological groups, and equally with the locally compact
nonarchimedean Hausdorff topological groups.

The core construction is the left translation stabilizer `MulAction.stabilizer G W` of a compact
open subset `W`: compactness of `W` and continuity of multiplication produce an open identity
neighbourhood `V` with `V * W ⊆ W`, so `V ∩ V⁻¹` lies inside the stabilizer, making it an open
subgroup. When `W` is nonempty the stabilizer is contained in a right translate of `W` and is
therefore compact; when `1 ∈ W` it lies inside `W` itself.

Applied to a compact clopen identity neighbourhood — supplied by a compact neighbourhood intersected
with a clopen basis in any weakly locally compact zero-dimensional group — this yields a basis of
compact open subgroups at `1` and establishes the full equivalence. We also record that every open
subgroup contained in a compact set is compact, that every compact open subgroup is profinite, and
that the compact open subgroups (as well as those contained in a fixed open subgroup) form a cofinal
directed basis of neighbourhoods of `1`.

## Main results

* `IsCompact.isOpen_mulAction_stabilizer`, `IsCompact.isCompact_mulAction_stabilizer`: the left
  translation stabilizer of a compact open set in a topological group is an open subgroup, and is
  compact when the set is nonempty (with additive forms for `AddAction.stabilizer`).
* `IsCompact.exists_compact_openSubgroup_subset`: any compact open neighbourhood of `1` contains a
  compact open subgroup.
* `IsTopologicalGroup.exists_compact_openSubgroup_subset`: in a weakly locally compact
  zero-dimensional topological group, every neighbourhood of `1` contains a compact open subgroup.
* `IsTopologicalGroup.nonarchimedeanGroup_of_weaklyLocallyCompactSpace`: a weakly locally compact
  zero-dimensional topological group is nonarchimedean.
* `NonarchimedeanGroup.exists_compact_openSubgroup_subset`: in a weakly locally compact
  nonarchimedean group, every neighbourhood of `1` contains a compact open subgroup.
* `IsTopologicalGroup.vanDantzig_tfae`: for a `T0` (equivalently Hausdorff) topological group, local
  compactness with total disconnectedness, local compactness with the nonarchimedean property, and
  existence of a compact open subgroup inside every identity neighbourhood are equivalent.
* `IsTopologicalGroup.nhds_one_hasBasis_compact_openSubgroup` and
  `IsTopologicalGroup.nhds_one_hasBasis_compact_openSubgroup_le`: the compact open subgroups (and
  those contained in a fixed open subgroup) form a basis of `𝓝 1`.
* `OpenSubgroup.isCompact_of_subset`: every open subgroup contained in a compact set is compact.
* `OpenSubgroup.directed_isCompact`, `OpenSubgroup.directed_isCompact_le`: the compact open
  subgroups form a downwards-directed family.
* `OpenSubgroup.toProfiniteGrp`: a compact open subgroup of a totally disconnected topological
  group as an object of `ProfiniteGrp`.
* `OpenSubgroup.eq_top_of_preconnectedSpace`: a preconnected topological group has no proper open
  subgroup.

## Implementation notes

`IsTopologicalGroup.nonarchimedeanGroup_of_weaklyLocallyCompactSpace` is a `theorem` rather than a
global `instance` to avoid creating a typeclass search cycle with
`NonarchimedeanGroup.instTotallySeparated` and
`instZeroDimensionalSpaceOfT2SpaceOfTotallyDisconnectedSpaceOfWeaklyLocallyCompactSpace`.

## References

* J. Bernstein, *Representations of `p`-adic groups*, lecture notes by K. E. Rumelhart, 1992,
  Ch. I, §1.1, Definition 1, p. 7.
* L. Kramer, *Locally compact groups*, 2002, Lemma 1.41, Proposition 1.43, and Theorem 1.44,
  pp. 17–19.
-/

public section

open Filter Topology
open scoped Pointwise

section TranslationStabilizer

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The left translation stabilizer of a compact open subset of a topological group is open. -/
@[to_additive /-- The left translation stabilizer of a compact open subset of a topological
additive group is open. -/]
theorem IsCompact.isOpen_mulAction_stabilizer {W : Set G} (hWc : IsCompact W) (hWo : IsOpen W) :
    IsOpen (MulAction.stabilizer G W : Set G) := by
  obtain ⟨V, hVo, h1V, hVW⟩ :=
    hWc.exists_isOpen_superset_mul_subset hWo (A := {1}) (by simp)
  have h1V' : (1 : G) ∈ V := h1V rfl
  have hmem : V ∩ V⁻¹ ∈ 𝓝 (1 : G) :=
    (hVo.inter hVo.inv).mem_nhds ⟨h1V', by simpa using h1V'⟩
  refine Subgroup.isOpen_of_mem_nhds _ (mem_of_superset hmem fun v hv ↦ ?_)
  rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨w, hw, rfl⟩
    exact hVW (Set.mul_mem_mul hv.1 hw)
  · intro w hw
    refine ⟨v⁻¹ * w, hVW (Set.mul_mem_mul hv.2 hw), by simp⟩

/-- The left translation stabilizer of a nonempty compact open subset of a topological group is
compact. -/
@[to_additive /-- The left translation stabilizer of a nonempty compact open subset of a
topological additive group is compact. -/]
theorem IsCompact.isCompact_mulAction_stabilizer {W : Set G} (hWc : IsCompact W) (hWo : IsOpen W)
    (hWne : W.Nonempty) : IsCompact (MulAction.stabilizer G W : Set G) := by
  obtain ⟨x, hx⟩ := hWne
  have hclosed : IsClosed (MulAction.stabilizer G W : Set G) :=
    Subgroup.isClosed_of_isOpen _ (hWc.isOpen_mulAction_stabilizer hWo)
  have hdiv : IsCompact (W / ({x} : Set G)) := by
    rw [div_eq_mul_inv]
    exact hWc.mul isCompact_singleton.inv
  exact hdiv.of_isClosed_subset hclosed (MulAction.stabilizer_subset_div_right hx)

/-- Every compact open neighbourhood of the identity in a topological group contains a compact open
subgroup, namely its left translation stabilizer. -/
@[to_additive /-- Every compact open neighbourhood of zero in a topological additive group contains
a compact open additive subgroup, namely its left translation stabilizer. -/]
theorem IsCompact.exists_compact_openSubgroup_subset {W : Set G} (hWc : IsCompact W)
    (hWo : IsOpen W) (h1W : (1 : G) ∈ W) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ W := by
  have hsub : (MulAction.stabilizer G W : Set G) ⊆ W := by
    simpa using MulAction.op_smul_set_stabilizer_subset h1W
  exact ⟨⟨MulAction.stabilizer G W, hWc.isOpen_mulAction_stabilizer hWo⟩,
    hWc.isCompact_mulAction_stabilizer hWo ⟨1, h1W⟩, hsub⟩

end TranslationStabilizer

section VanDantzig

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- **Van Dantzig's theorem.** In a weakly locally compact zero-dimensional topological group, every
neighbourhood of `1` contains a compact open subgroup. -/
@[to_additive /-- **Van Dantzig's theorem.** In a weakly locally compact zero-dimensional
topological additive group, every neighbourhood of `0` contains a compact open additive
subgroup. -/]
theorem IsTopologicalGroup.exists_compact_openSubgroup_subset [IsTopologicalGroup G]
    [WeaklyLocallyCompactSpace G] [ZeroDimensionalSpace G] {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ U := by
  obtain ⟨C, hCc, hCn⟩ := exists_compact_mem_nhds (1 : G)
  obtain ⟨W, ⟨hWcl, h1W⟩, hWsub⟩ := (nhds_basis_isClopen (1 : G)).mem_iff.mp (inter_mem hU hCn)
  have hWc : IsCompact W :=
    hCc.of_isClosed_subset hWcl.isClosed (hWsub.trans Set.inter_subset_right)
  obtain ⟨K, hKc, hKW⟩ := hWc.exists_compact_openSubgroup_subset hWcl.isOpen h1W
  exact ⟨K, hKc, hKW.trans (hWsub.trans Set.inter_subset_left)⟩

/-- A weakly locally compact zero-dimensional topological group is nonarchimedean. -/
@[to_additive /-- A weakly locally compact zero-dimensional topological additive group is
nonarchimedean. -/]
theorem IsTopologicalGroup.nonarchimedeanGroup_of_weaklyLocallyCompactSpace [IsTopologicalGroup G]
    [WeaklyLocallyCompactSpace G] [ZeroDimensionalSpace G] : NonarchimedeanGroup G where
  is_nonarchimedean _ hU :=
    let ⟨K, _, hKU⟩ := exists_compact_openSubgroup_subset hU
    ⟨K, hKU⟩

/-- In a weakly locally compact nonarchimedean group, every neighbourhood of `1` contains a compact
open subgroup. -/
@[to_additive /-- In a weakly locally compact nonarchimedean additive group, every neighbourhood of
`0` contains a compact open additive subgroup. -/]
theorem NonarchimedeanGroup.exists_compact_openSubgroup_subset [NonarchimedeanGroup G]
    [WeaklyLocallyCompactSpace G] {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ U := by
  obtain ⟨C, hCc, hCn⟩ := exists_compact_mem_nhds (1 : G)
  obtain ⟨K, hKsub⟩ := NonarchimedeanGroup.is_nonarchimedean (U ∩ C) (inter_mem hU hCn)
  exact ⟨K, hCc.of_isClosed_subset K.isClosed (hKsub.trans Set.inter_subset_right),
    hKsub.trans Set.inter_subset_left⟩

/-- In a weakly locally compact zero-dimensional topological group, the compact open subgroups form
a neighbourhood basis of `1`. -/
@[to_additive /-- In a weakly locally compact zero-dimensional topological additive group, the
compact open additive subgroups form a neighbourhood basis of `0`. -/]
theorem IsTopologicalGroup.nhds_one_hasBasis_compact_openSubgroup [IsTopologicalGroup G]
    [WeaklyLocallyCompactSpace G] [ZeroDimensionalSpace G] :
    (𝓝 (1 : G)).HasBasis (fun K : OpenSubgroup G ↦ IsCompact (K : Set G)) fun K ↦ (K : Set G) :=
  ⟨fun _ ↦ ⟨fun hU ↦ exists_compact_openSubgroup_subset hU,
    fun ⟨K, _, hKU⟩ ↦ mem_of_superset K.mem_nhds_one hKU⟩⟩

/-- In a weakly locally compact zero-dimensional topological group, the compact open subgroups
contained in any given open subgroup `K₀` still form a neighbourhood basis of `1`. -/
@[to_additive /-- In a weakly locally compact zero-dimensional topological additive group, the
compact open additive subgroups contained in any given open additive subgroup `K₀` still form a
neighbourhood basis of `0`. -/]
theorem IsTopologicalGroup.nhds_one_hasBasis_compact_openSubgroup_le [IsTopologicalGroup G]
    [WeaklyLocallyCompactSpace G] [ZeroDimensionalSpace G] (K₀ : OpenSubgroup G) :
    (𝓝 (1 : G)).HasBasis (fun K : OpenSubgroup G ↦ IsCompact (K : Set G) ∧ K ≤ K₀)
      fun K ↦ (K : Set G) := by
  refine ⟨fun U ↦ ⟨fun hU ↦ ?_, fun ⟨K, _, hKU⟩ ↦ mem_of_superset K.mem_nhds_one hKU⟩⟩
  obtain ⟨K, hKc, hKsub⟩ := exists_compact_openSubgroup_subset (inter_mem hU K₀.mem_nhds_one)
  exact ⟨K, ⟨hKc, hKsub.trans Set.inter_subset_right⟩, hKsub.trans Set.inter_subset_left⟩

/-- **Van Dantzig's characterization of locally profinite groups.** For a `T0` (equivalently
Hausdorff) topological group `G`, the following are equivalent:
1. `G` is locally compact and totally disconnected;
2. `G` is locally compact and nonarchimedean;
3. every neighbourhood of `1` contains a compact open subgroup. -/
@[to_additive /-- **Van Dantzig's characterization of locally profinite additive groups.** For a
`T0` (equivalently Hausdorff) topological additive group `G`, the following are equivalent:
1. `G` is locally compact and totally disconnected;
2. `G` is locally compact and nonarchimedean;
3. every neighbourhood of `0` contains a compact open additive subgroup. -/]
theorem IsTopologicalGroup.vanDantzig_tfae (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T0Space G] :
    List.TFAE
      [LocallyCompactSpace G ∧ TotallyDisconnectedSpace G,
       LocallyCompactSpace G ∧ NonarchimedeanGroup G,
       ∀ U ∈ 𝓝 (1 : G), ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ U] := by
  tfae_have 1 → 3 := fun ⟨hLC, hTD⟩ U hU ↦
    IsTopologicalGroup.exists_compact_openSubgroup_subset hU
  tfae_have 3 → 2 := fun h ↦ by
    obtain ⟨K, hKc, _⟩ := h Set.univ univ_mem
    exact ⟨hKc.locallyCompactSpace_of_mem_nhds_of_group K.mem_nhds_one,
      ⟨fun U hU ↦ let ⟨V, _, hVU⟩ := h U hU; ⟨V, hVU⟩⟩⟩
  tfae_have 2 → 1 := fun ⟨hLC, hNA⟩ ↦ ⟨hLC, inferInstance⟩
  tfae_finish

end VanDantzig

namespace OpenSubgroup

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- Every open subgroup contained in a compact set is compact, since open subgroups of a group
with separately continuous multiplication are closed. -/
@[to_additive /-- Every open additive subgroup contained in a compact set is compact, since open
additive subgroups of an additive group with separately continuous addition are closed. -/]
theorem isCompact_of_subset [SeparatelyContinuousMul G] {K : OpenSubgroup G} {C : Set G}
    (hC : IsCompact C) (hKC : (K : Set G) ⊆ C) : IsCompact (K : Set G) :=
  hC.of_isClosed_subset K.isClosed hKC

/-- The compact open subgroups of a topological group with separately continuous multiplication
form a downwards-directed family under inclusion. -/
@[to_additive /-- The compact open additive subgroups of a topological additive group with
separately continuous addition form a downwards-directed family under inclusion. -/]
theorem directed_isCompact [SeparatelyContinuousMul G] :
    Directed (· ≥ ·)
      (Subtype.val : {K : OpenSubgroup G // IsCompact (K : Set G)} → OpenSubgroup G) :=
  fun K₁ K₂ ↦
    ⟨⟨K₁.1 ⊓ K₂.1, isCompact_of_subset K₁.2 Set.inter_subset_left⟩, inf_le_left, inf_le_right⟩

/-- The compact open subgroups contained in a fixed open subgroup `K₀` form a downwards-directed
family under inclusion. -/
@[to_additive /-- The compact open additive subgroups contained in a fixed open additive subgroup
`K₀` form a downwards-directed family under inclusion. -/]
theorem directed_isCompact_le [SeparatelyContinuousMul G] (K₀ : OpenSubgroup G) :
    Directed (· ≥ ·) (Subtype.val :
      {K : OpenSubgroup G // IsCompact (K : Set G) ∧ K ≤ K₀} → OpenSubgroup G) :=
  fun K₁ K₂ ↦
    ⟨⟨K₁.1 ⊓ K₂.1, isCompact_of_subset K₁.2.1 Set.inter_subset_left, inf_le_left.trans K₁.2.2⟩,
      inf_le_left, inf_le_right⟩

/-- A compact open subgroup of a totally disconnected topological group, viewed as an object of
`ProfiniteGrp`. -/
@[to_additive /-- A compact open additive subgroup of a totally disconnected topological additive
group, viewed as an object of `ProfiniteAddGrp`. -/]
abbrev toProfiniteGrp [IsTopologicalGroup G] [TotallyDisconnectedSpace G]
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) : ProfiniteGrp :=
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  ProfiniteGrp.of K

/-- The underlying type of `K.toProfiniteGrp hK` is `K`. -/
@[to_additive /-- The underlying type of `K.toProfiniteAddGrp hK` is `K`. -/]
theorem coe_toProfiniteGrp [IsTopologicalGroup G] [TotallyDisconnectedSpace G]
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    (K.toProfiniteGrp hK : Type _) = K :=
  rfl

/-- Every open subgroup of a preconnected topological group with separately continuous
multiplication is the whole group. -/
@[to_additive /-- Every open additive subgroup of a preconnected topological additive group with
separately continuous addition is the whole group. -/]
theorem eq_top_of_preconnectedSpace [SeparatelyContinuousMul G] [PreconnectedSpace G]
    (U : OpenSubgroup G) : U = ⊤ :=
  SetLike.coe_injective (U.isClopen.eq_univ ⟨1, U.one_mem⟩)

end OpenSubgroup
