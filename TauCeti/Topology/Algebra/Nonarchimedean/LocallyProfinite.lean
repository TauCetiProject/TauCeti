/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
public import Mathlib.Topology.Separation.Connected
public import Mathlib.Topology.Separation.Regular
public import TauCeti.Topology.Algebra.Group.OpenSubgroup.Compact
public import TauCeti.Topology.Algebra.Nonarchimedean.Basic

/-!
# Van Dantzig's theorem and compact open subgroup bases in locally profinite groups

A Hausdorff topological group `G` is *locally profinite* (an *ℓ-group*) when the neighbourhoods of
`1` admit a basis of compact open subgroups. Van Dantzig's theorem shows that for a `T₀` (hence
Hausdorff) topological group `G`, three conditions are equivalent:

1. `G` is locally compact and totally disconnected (`LocallyCompactSpace G` and
   `TotallyDisconnectedSpace G`);
2. `G` is locally compact and nonarchimedean (`LocallyCompactSpace G` and `NonarchimedeanGroup G`);
3. every neighbourhood of `1` contains a compact open subgroup.

The implications separate cleanly according to the minimal hypotheses each uses:

* **Zero-dimensional locally compact case (`(1) ⇒ (3)` and `(1) ⇒ (2)`):** in any weakly locally
  compact zero-dimensional topological group (including every locally compact totally disconnected
  topological group, via Mathlib's `ZeroDimensionalSpace` instance), intersecting an identity
  neighbourhood with a compact identity neighbourhood and extracting a clopen identity
  neighbourhood inside it produces a compact clopen neighbourhood `C` of `1`; its left translation
  stabilizer is a compact open subgroup inside `C`
  (`TauCeti.IsTopologicalGroup.exists_openSubgroup_isCompact_subset`). In particular, `G` is a
  `NonarchimedeanGroup`
  (`TauCeti.IsTopologicalGroup.nonarchimedeanGroup_of_weaklyLocallyCompactSpace`).
* **Nonarchimedean locally compact case (`(2) ⇒ (3)`):** in any weakly locally compact
  nonarchimedean group (without any separation axiom), intersecting an identity neighbourhood with a
  compact neighbourhood `K` of `1` and picking an open subgroup inside that intersection gives a
  closed — hence compact — open subgroup inside the given neighbourhood
  (`NonarchimedeanGroup.exists_openSubgroup_isCompact_subset`, packaged as the filter basis
  `NonarchimedeanGroup.nhds_one_hasBasis_isCompact_openSubgroup`).
* **From compact open subgroups back (`(3) ⇒ (1), (2)`):** a single compact open subgroup makes `G`
  locally compact (`OpenSubgroup.locallyCompactSpace_of_isCompact`), and when `G` is `T₀` (hence
  Hausdorff) the nonarchimedean property makes `G` totally separated and therefore totally
  disconnected.

We also record the profinite structure of compact open subgroups: whenever `U : OpenSubgroup G` is
compact and `NonarchimedeanGroup U` holds (for example via `OpenSubgroup.instNonarchimedeanGroup`
when `G` is nonarchimedean or weakly locally compact and zero-dimensional), the open normal
subgroups of `U` (each of finite index in `U`) push forward along `U.mapSubtype` to a neighbourhood
basis of `1` in `G` consisting of open subgroups contained in `U`
(`OpenSubgroup.nhds_one_hasBasis_mapSubtype_openNormalSubgroup`), via Mathlib's
`IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one`.

## Main results

* `TauCeti.IsTopologicalGroup.exists_openSubgroup_isCompact_subset` and
  `TauCeti.IsTopologicalGroup.nonarchimedeanGroup_of_weaklyLocallyCompactSpace`: Van Dantzig's
  construction for weakly locally compact zero-dimensional topological groups.
* `NonarchimedeanGroup.exists_openSubgroup_isCompact_subset`,
  `NonarchimedeanGroup.nhds_one_hasBasis_isCompact_openSubgroup`, and
  `NonarchimedeanGroup.nhds_one_hasBasis_isCompact_openSubgroup_le`: compact open subgroup bases of
  `𝓝 1` (globally, and restricted below any fixed compact open subgroup `U₀`).
* `OpenSubgroup.nhds_one_hasBasis_mapSubtype_openNormalSubgroup`: open normal subgroups of a
  compact nonarchimedean open subgroup `U` form a neighbourhood basis of `1` in `G`.
* `TauCeti.IsTopologicalGroup.locallyProfinite_tfae` and its pairwise `iff` corollaries: the
  three-way characterization of locally profinite groups.

## References

* D. van Dantzig, *Zur topologischen Algebra. III. Brouwersche und Cantorsche Gruppen*,
  Compositio Math. 3 (1936), 408–426.
* J. Bernstein, *Representations of p-adic groups* (Harvard lectures, 1992, notes by K. Rumelhart),
  Chapter I, §1.1, Definition 1, p. 7.
* L. Kramer, *Locally Compact Groups and Lie Groups*, Chapter 1 (version of 19 May 2020),
  Proposition 1.43 and Theorem 1.44, pp. 18–19.
-/

public section

open Filter Set Topology

namespace TauCeti

section ZeroDimensional

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [WeaklyLocallyCompactSpace G] [ZeroDimensionalSpace G]

/-- **Van Dantzig's theorem (existence form).** In a weakly locally compact zero-dimensional
topological group, every identity neighbourhood contains a compact open subgroup. This covers all
locally compact totally disconnected topological groups, since such groups are Hausdorff and hence
zero-dimensional. -/
@[to_additive IsTopologicalAddGroup.exists_openAddSubgroup_isCompact_subset
/-- **Van Dantzig's theorem (additive existence form).** In a weakly locally compact
zero-dimensional topological additive group, every neighbourhood of zero contains a compact open
additive subgroup. -/]
theorem IsTopologicalGroup.exists_openSubgroup_isCompact_subset {U : Set G}
    (hU : U ∈ 𝓝 (1 : G)) :
    ∃ H : OpenSubgroup G, IsCompact (H : Set G) ∧ (H : Set G) ⊆ U := by
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G)
  obtain ⟨C, ⟨hCclopen, h1C⟩, hCUK⟩ := (nhds_basis_isClopen (1 : G)).mem_iff.mp (inter_mem hU hK1)
  have hCcompact : IsCompact C := hK.of_isClosed_subset hCclopen.isClosed
    (hCUK.trans inter_subset_right)
  obtain ⟨H, hHc, hHC⟩ :=
    exists_openSubgroup_isCompact_subset_of_isCompact_of_isOpen hCcompact hCclopen.isOpen h1C
  exact ⟨H, hHc, hHC.trans (hCUK.trans inter_subset_left)⟩

/-- **A weakly locally compact zero-dimensional topological group is nonarchimedean.** This covers
all locally compact totally disconnected topological groups (as well as all compact totally
disconnected topological groups), which are Hausdorff and hence zero-dimensional. -/
@[to_additive IsTopologicalAddGroup.nonarchimedeanAddGroup_of_weaklyLocallyCompactSpace
/-- **A weakly locally compact zero-dimensional topological additive group is nonarchimedean.**
This covers all locally compact totally disconnected topological additive groups. -/]
instance (priority := 100) IsTopologicalGroup.nonarchimedeanGroup_of_weaklyLocallyCompactSpace :
    NonarchimedeanGroup G where
  is_nonarchimedean _ hU :=
    let ⟨H, _, hHU⟩ := exists_openSubgroup_isCompact_subset hU
    ⟨H, hHU⟩

end ZeroDimensional

end TauCeti

namespace NonarchimedeanGroup

variable {G : Type*} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]

/-- **Every identity neighbourhood in a weakly locally compact nonarchimedean group contains a
compact open subgroup.** Intersecting the neighbourhood with a compact identity neighbourhood `K`
and choosing an open subgroup inside that intersection gives a closed — hence compact — subgroup.
No separation axiom on `G` is required. -/
@[to_additive
/-- **Every neighbourhood of zero in a weakly locally compact nonarchimedean additive group
contains a compact open additive subgroup.** No separation axiom on `G` is required. -/]
theorem exists_openSubgroup_isCompact_subset [WeaklyLocallyCompactSpace G] {U : Set G}
    (hU : U ∈ 𝓝 (1 : G)) :
    ∃ H : OpenSubgroup G, IsCompact (H : Set G) ∧ (H : Set G) ⊆ U := by
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G)
  obtain ⟨H, hH⟩ := is_nonarchimedean (U ∩ K) (inter_mem hU hK1)
  exact ⟨H, H.isCompact_of_subset hK (hH.trans inter_subset_right), hH.trans inter_subset_left⟩

/-- **The compact open subgroups form a basis of `𝓝 1`** in any weakly locally compact
nonarchimedean group (and hence, by typeclass synthesis, in any locally compact totally
disconnected topological group). -/
@[to_additive
/-- **The compact open additive subgroups form a basis of `𝓝 0`** in any weakly locally compact
nonarchimedean additive group (and hence in any locally compact totally disconnected topological
additive group). -/]
theorem nhds_one_hasBasis_isCompact_openSubgroup [WeaklyLocallyCompactSpace G] :
    (𝓝 (1 : G)).HasBasis (fun H : OpenSubgroup G ↦ IsCompact (H : Set G)) fun H ↦ (H : Set G) :=
  ⟨fun _ ↦ ⟨exists_openSubgroup_isCompact_subset,
    fun ⟨H, _, hH⟩ ↦ mem_of_superset H.mem_nhds_one hH⟩⟩

/-- **The compact open subgroups contained in a fixed compact open subgroup `U₀` form a basis of
`𝓝 1`** in any nonarchimedean group. Ambient local compactness need not be assumed separately, as
`U₀` already supplies compactness. -/
@[to_additive
/-- **The compact open additive subgroups contained in a fixed compact open additive subgroup `U₀`
form a basis of `𝓝 0`** in any nonarchimedean additive group. -/]
theorem nhds_one_hasBasis_isCompact_openSubgroup_le {U₀ : OpenSubgroup G}
    (hU₀ : IsCompact (U₀ : Set G)) :
    (𝓝 (1 : G)).HasBasis (fun U : OpenSubgroup G ↦ IsCompact (U : Set G) ∧ U ≤ U₀)
      fun U ↦ (U : Set G) := by
  refine ⟨fun W ↦ ⟨fun hW ↦ ?_, fun ⟨U, _, hUW⟩ ↦ mem_of_superset U.mem_nhds_one hUW⟩⟩
  obtain ⟨V, hV⟩ := is_nonarchimedean W hW
  exact ⟨V ⊓ U₀, ⟨U₀.isCompact_inf_right V hU₀, inf_le_right⟩, inter_subset_left.trans hV⟩

end NonarchimedeanGroup

namespace OpenSubgroup

/-- **Profinite neighbourhood basis inside a compact nonarchimedean open subgroup.** If `U` is a
compact open subgroup of `G` and `U` is nonarchimedean in the subspace topology (synthesized
automatically under `[NonarchimedeanGroup G]` or `[IsTopologicalGroup G]
[WeaklyLocallyCompactSpace G] [ZeroDimensionalSpace G]`), then the open normal subgroups
`N : OpenNormalSubgroup U` (each of finite index in `U`) push forward via `U.mapSubtype` to a basis
of `𝓝 (1 : G)`. No continuity of the ambient group operations on `G` is required. -/
@[to_additive
/-- **Profinite neighbourhood basis inside a compact nonarchimedean open additive subgroup.** If `U`
is a compact open additive subgroup of `G` and `U` is nonarchimedean in the subspace topology, then
the open normal additive subgroups `N : OpenNormalAddSubgroup U` push forward via `U.mapSubtype` to
a basis of `𝓝 (0 : G)`. No continuity of the ambient group operations on `G` is required. -/]
theorem nhds_one_hasBasis_mapSubtype_openNormalSubgroup {G : Type*} [Group G] [TopologicalSpace G]
    {U : OpenSubgroup G} [NonarchimedeanGroup U] (hU : IsCompact (U : Set G)) :
    (𝓝 (1 : G)).HasBasis (fun _ : OpenNormalSubgroup U ↦ True)
      fun N ↦ ((U.mapSubtype N.toOpenSubgroup : OpenSubgroup G) : Set G) := by
  have : CompactSpace U := isCompact_iff_compactSpace.mp hU
  refine ⟨fun W ↦ ⟨fun hW ↦ ?_, fun ⟨N, _, hNW⟩ ↦
    mem_of_superset (U.mapSubtype N.toOpenSubgroup).mem_nhds_one hNW⟩⟩
  have hpre : (Subtype.val : U → G) ⁻¹' W ∈ 𝓝 (1 : U) :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds hW
  obtain ⟨K, hKW⟩ := NonarchimedeanGroup.is_nonarchimedean _ hpre
  obtain ⟨N, hNK⟩ :=
    IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one K.isClopen K.one_mem
  refine ⟨N, trivial, ?_⟩
  rw [U.coe_mapSubtype]
  rintro _ ⟨x, hxN, rfl⟩
  exact hKW (hNK hxN)

end OpenSubgroup

namespace TauCeti

section TFAE

/-- A topological group is locally compact and nonarchimedean if and only if every identity
neighbourhood contains a compact open subgroup. No separation axiom on `G` is required. -/
@[to_additive
/-- A topological additive group is locally compact and nonarchimedean if and only if every
neighbourhood of zero contains a compact open additive subgroup. No separation axiom on `G` is
required. -/]
theorem locallyCompactSpace_and_nonarchimedeanGroup_iff_exists_openSubgroup_isCompact
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    LocallyCompactSpace G ∧ NonarchimedeanGroup G ↔
      ∀ U ∈ 𝓝 (1 : G), ∃ H : OpenSubgroup G, IsCompact (H : Set G) ∧ (H : Set G) ⊆ U := by
  refine ⟨fun ⟨_, _⟩ _ hU ↦ NonarchimedeanGroup.exists_openSubgroup_isCompact_subset hU, fun h ↦ ?_⟩
  obtain ⟨H₀, hH₀, -⟩ := h univ univ_mem
  exact ⟨H₀.locallyCompactSpace_of_isCompact hH₀,
    { is_nonarchimedean := fun U hU ↦ let ⟨H, _, hHU⟩ := h U hU; ⟨H, hHU⟩ }⟩

open scoped List in
/-- **Van Dantzig's characterization of locally profinite groups.** For a `T₀` (hence Hausdorff)
topological group `G`, the following are equivalent:
1. `G` is locally compact and totally disconnected;
2. `G` is locally compact and nonarchimedean (every neighbourhood of `1` contains an open subgroup);
3. every neighbourhood of `1` contains a compact open subgroup. -/
@[to_additive IsTopologicalAddGroup.locallyProfinite_tfae
/-- **Van Dantzig's characterization of locally profinite additive groups.** For a `T₀` (hence
Hausdorff) topological additive group `G`, the following are equivalent:
1. `G` is locally compact and totally disconnected;
2. `G` is locally compact and nonarchimedean (every neighbourhood of `0` contains an open additive
   subgroup);
3. every neighbourhood of `0` contains a compact open additive subgroup. -/]
theorem IsTopologicalGroup.locallyProfinite_tfae (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T0Space G] :
    [LocallyCompactSpace G ∧ TotallyDisconnectedSpace G,
      LocallyCompactSpace G ∧ NonarchimedeanGroup G,
      ∀ U ∈ 𝓝 (1 : G), ∃ H : OpenSubgroup G, IsCompact (H : Set G) ∧ (H : Set G) ⊆ U].TFAE := by
  tfae_have 1 → 2
  | ⟨hLC, _⟩ => ⟨hLC, inferInstance⟩
  tfae_have 2 → 3
  | h => (locallyCompactSpace_and_nonarchimedeanGroup_iff_exists_openSubgroup_isCompact G).mp h
  tfae_have 3 → 1
  | h => by
    obtain ⟨hLC, _⟩ :=
      (locallyCompactSpace_and_nonarchimedeanGroup_iff_exists_openSubgroup_isCompact G).mpr h
    exact ⟨hLC, inferInstance⟩
  tfae_finish

/-- A `T₀` topological group is locally compact and totally disconnected if and only if every
identity neighbourhood contains a compact open subgroup. -/
@[to_additive
/-- A `T₀` topological additive group is locally compact and totally disconnected if and only if
every neighbourhood of zero contains a compact open additive subgroup. -/]
theorem locallyCompactSpace_and_totallyDisconnectedSpace_iff_exists_openSubgroup_isCompact
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T0Space G] :
    LocallyCompactSpace G ∧ TotallyDisconnectedSpace G ↔
      ∀ U ∈ 𝓝 (1 : G), ∃ H : OpenSubgroup G, IsCompact (H : Set G) ∧ (H : Set G) ⊆ U :=
  (IsTopologicalGroup.locallyProfinite_tfae G).out 1 3

/-- A weakly locally compact `T₀` topological group is totally disconnected if and only if it is
nonarchimedean. -/
@[to_additive IsTopologicalAddGroup.totallyDisconnectedSpace_iff_nonarchimedeanAddGroup
/-- A weakly locally compact `T₀` topological additive group is totally disconnected if and only if
it is nonarchimedean. -/]
theorem IsTopologicalGroup.totallyDisconnectedSpace_iff_nonarchimedeanGroup (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [WeaklyLocallyCompactSpace G] [T0Space G] :
    TotallyDisconnectedSpace G ↔ NonarchimedeanGroup G :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

end TFAE

end TauCeti
