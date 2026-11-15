/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.TFAE
public import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
public import Mathlib.Topology.Separation.Connected
public import Mathlib.Topology.Separation.Regular
public import TauCeti.Topology.Algebra.Group.OpenSubgroup.Basic
public import TauCeti.Topology.Algebra.Nonarchimedean.Basic
import Mathlib.Topology.Algebra.ClopenNhdofOne
import TauCeti.Topology.Algebra.Group.Pointwise
import TauCeti.Topology.Algebra.MulAction.Stabilizer
import TauCeti.Topology.Algebra.Nonarchimedean.OpenSubgroupBasis

/-!
# Locally profinite groups and van Dantzig's theorem

A Hausdorff topological group `G` is *locally profinite* (an *l-group*) when it is locally compact
and totally disconnected. In Mathlib's unbundled typeclass hierarchy, `[IsTopologicalGroup G]` and
`[TotallyDisconnectedSpace G]` already synthesize `T2Space G`, and together with
`[WeaklyLocallyCompactSpace G]` they synthesize `ZeroDimensionalSpace G`.

Van Dantzig's theorem identifies locally profinite groups among all Hausdorff topological groups by
four equivalent conditions:
1. `G` is locally compact and totally disconnected
   (`LocallyCompactSpace G ∧ TotallyDisconnectedSpace G`);
2. `G` is locally compact and nonarchimedean (`LocallyCompactSpace G ∧ NonarchimedeanGroup G`);
3. every neighbourhood of `1` contains a compact open subgroup;
4. the compact open subgroups form a filter basis of `𝓝 (1 : G)`.

For `(1) ⇒ (4)`, intersecting a closed compact identity neighbourhood with the clopen basis of
`ZeroDimensionalSpace G` produces a compact clopen identity neighbourhood `C`, whose
left-translation stabilizer `OpenSubgroup.stabilizer G` is an open subgroup inside `C`. This step
requires neither `T2Space G` nor full `LocallyCompactSpace G`: `[WeaklyLocallyCompactSpace G]` and
`[ZeroDimensionalSpace G]` suffice to register `NonarchimedeanGroup G`, covering both profinite and
locally profinite groups. In any weakly locally compact nonarchimedean group, intersecting with a
compact identity neighbourhood then makes open subgroup refinements compact, yielding the basis of
compact open subgroups at `1` (and coset bases at every `g : G`). Conversely, a single compact open
subgroup supplies local compactness via left translation, and the clopen cosets of open subgroups
separate points in a Hausdorff group, making `G` totally separated and hence totally disconnected.

In a locally profinite group, every compact open subgroup `U₀` inherits `IsTopologicalGroup U₀`,
`TotallyDisconnectedSpace U₀` (via `Subtype.totallyDisconnectedSpace`), `T2Space U₀`,
`NonarchimedeanGroup U₀` (via `OpenSubgroup.instNonarchimedeanGroup`), and (via
`isCompact_iff_compactSpace`) `CompactSpace U₀`, so `U₀` is a profinite group in the unbundled
sense; in particular, every identity neighbourhood of `G` contains a compact open subgroup `V ≤ U₀`
whose trace in `U₀` is normal. Moreover, the compact open subgroups contained in `U₀` form a
basis of `𝓝 (1 : G)` in addition to being downward-directed and coinitial in `OpenSubgroup G`.

## Main results

* `OpenSubgroup.nhds_one_hasBasis_isCompact_and_le`: in a nonarchimedean group, compact open
  subgroups contained in a given compact open subgroup `U₀` form a basis of `𝓝 (1 : G)`.
* `OpenSubgroup.exists_isCompact_le_normal_of_mem_nhds_one`: inside any compact open subgroup `U₀`
  of a totally disconnected topological group, every identity neighbourhood contains a compact open
  subgroup `V ≤ U₀` normal in `U₀`.
* `NonarchimedeanGroup.exists_openSubgroup_isCompact_subset`,
  `NonarchimedeanGroup.nhds_one_hasBasis_isCompact_openSubgroup`,
  `NonarchimedeanGroup.nhds_hasBasis_isCompact_openSubgroup`,
  `NonarchimedeanGroup.isCoinitial_isCompact_openSubgroup`: compact open subgroup existence,
  neighbourhood bases, and coinitiality in weakly locally compact nonarchimedean groups.
* `IsTopologicalGroup.nonarchimedeanGroup_of_weaklyLocallyCompactSpace`: weakly locally compact
  zero-dimensional topological groups (including all profinite and locally profinite groups) are
  nonarchimedean.
* `IsTopologicalGroup.locallyCompactSpace_and_totallyDisconnectedSpace_tfae` and its pairwise `↔`
  corollaries: van Dantzig's characterization of locally profinite groups, with additive
  counterparts throughout.

## References

* J. Bernstein, *Representations of p-adic groups*, Harvard lectures written by K. Rumelhart
  (1992), Chapter I, §1.1, Definition 1, p. 7.
* L. Kramer, *Locally Compact Groups and Lie Groups*, Chapter 1 (2020), Lemma 1.41,
  Proposition 1.43, and Theorem 1.44, pp. 17–19.
* D. van Dantzig, *Zur topologischen Algebra. III. Brouwersche und Cantorsche Gruppen*,
  Compositio Mathematica 3 (1936), 408–426.
-/

public section

open Filter Set
open scoped Pointwise Topology

namespace OpenSubgroup

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- In a nonarchimedean group (in particular, in any locally profinite group), the compact open
subgroups contained in a given compact open subgroup `U₀` form a basis of `𝓝 (1 : G)`. -/
@[to_additive /-- In a nonarchimedean additive group (in particular, in any locally profinite
additive group), the compact open additive subgroups contained in a given compact open additive
subgroup `U₀` form a basis of `𝓝 (0 : G)`. -/]
theorem nhds_one_hasBasis_isCompact_and_le [NonarchimedeanGroup G] {U₀ : OpenSubgroup G}
    (hU₀ : IsCompact (U₀ : Set G)) :
    (𝓝 (1 : G)).HasBasis (fun V : OpenSubgroup G ↦ IsCompact (V : Set G) ∧ V ≤ U₀)
      fun V ↦ (V : Set G) :=
  (NonarchimedeanGroup.nhds_one_hasBasis_openSubgroup G).to_hasBasis'
    (fun W _ ↦ ⟨U₀ ⊓ W, ⟨(U₀ ⊓ W).isCompact_of_subset_isCompact hU₀ inf_le_left, inf_le_left⟩,
      inf_le_right⟩)
    fun V _ ↦ V.mem_nhds_one

/-- **Profinite normal refinement inside a compact open subgroup.** Because a compact open subgroup
`U₀` of a totally disconnected topological group is profinite, every identity neighbourhood of `G`
contains a compact open subgroup `V ≤ U₀` whose trace `V.toSubgroup.subgroupOf U₀.toSubgroup` is
normal in `U₀`. -/
@[to_additive /-- **Profinite normal refinement inside a compact open additive subgroup.** Because
a compact open additive subgroup `U₀` of a totally disconnected topological additive group is
profinite, every neighbourhood of `0` in `G` contains a compact open additive subgroup `V ≤ U₀`
whose trace `V.toAddSubgroup.addSubgroupOf U₀.toAddSubgroup` is normal in `U₀`. -/]
theorem exists_isCompact_le_normal_of_mem_nhds_one [IsTopologicalGroup G]
    [TotallyDisconnectedSpace G] {U₀ : OpenSubgroup G} (hU₀ : IsCompact (U₀ : Set G)) {s : Set G}
    (hs : s ∈ 𝓝 (1 : G)) :
    ∃ V : OpenSubgroup G,
      IsCompact (V : Set G) ∧ V ≤ U₀ ∧ (V.toSubgroup.subgroupOf U₀.toSubgroup).Normal ∧
        (V : Set G) ⊆ s := by
  -- Work in the underlying subgroup `U₀' = U₀.toSubgroup`, which is compact and open in `G` and
  -- therefore profinite in the subspace topology.
  let U₀' : Subgroup G := U₀.toSubgroup
  have hU₀'_compact : IsCompact (U₀' : Set G) := by simpa [U₀'] using hU₀
  have hU₀'_open : IsOpen (U₀' : Set G) := by simpa [U₀'] using U₀.isOpen
  have : CompactSpace U₀' := isCompact_iff_compactSpace.mp hU₀'_compact
  have hs_sub : (((↑) : U₀' → G) ⁻¹' s) ∈ 𝓝 (1 : U₀') :=
    continuous_subtype_val.continuousAt hs
  obtain ⟨W, hWs, hW_open, h1W⟩ := mem_nhds_iff.mp hs_sub
  obtain ⟨N, hNW⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (G := U₀') hW_open h1W
  -- Push `N` forward along the open subtype inclusion `U₀' →* G`.
  let H_sub : Subgroup G := N.toSubgroup.map U₀'.subtype
  have hH_open : IsOpen (H_sub : Set G) := by
    rw [Subgroup.coe_map, Subgroup.coe_subtype]
    exact hU₀'_open.isOpenMap_subtype_val _ N.toOpenSubgroup.isOpen
  let V : OpenSubgroup G := ⟨H_sub, hH_open⟩
  have hVU₀ : V ≤ U₀ := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hsub : V.toSubgroup.subgroupOf U₀' = N.toSubgroup := by
    ext x
    simp [V, H_sub, Subgroup.mem_subgroupOf]
  refine ⟨V, V.isCompact_of_subset_isCompact hU₀ hVU₀, hVU₀, ?_, ?_⟩
  · rw [hsub]
    exact N.isNormal'
  · rintro _ ⟨x, hxN, rfl⟩
    exact hWs (hNW hxN)

end OpenSubgroup

namespace NonarchimedeanGroup

variable {G : Type*} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  [WeaklyLocallyCompactSpace G]

/-- In a weakly locally compact nonarchimedean group, every identity neighbourhood contains a
compact open subgroup: intersect with a compact identity neighbourhood and take an open subgroup
inside it. -/
@[to_additive /-- In a weakly locally compact nonarchimedean additive group, every neighbourhood of
`0` contains a compact open additive subgroup: intersect with a compact neighbourhood of `0` and
take an open additive subgroup inside it. -/]
theorem exists_openSubgroup_isCompact_subset {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ H : OpenSubgroup G, IsCompact (H : Set G) ∧ (H : Set G) ⊆ U := by
  obtain ⟨K, hK_compact, hK_mem⟩ := exists_compact_mem_nhds (1 : G)
  obtain ⟨H, hH⟩ := is_nonarchimedean (U ∩ K) (inter_mem hU hK_mem)
  exact ⟨H, H.isCompact_of_subset_isCompact hK_compact (hH.trans inter_subset_right),
    hH.trans inter_subset_left⟩

/-- In a weakly locally compact nonarchimedean group (and hence in every locally profinite group),
the compact open subgroups form a basis of `𝓝 (1 : G)`. -/
@[to_additive /-- In a weakly locally compact nonarchimedean additive group (and hence in every
locally profinite additive group), the compact open additive subgroups form a basis of
`𝓝 (0 : G)`. -/]
theorem nhds_one_hasBasis_isCompact_openSubgroup (G : Type*) [Group G] [TopologicalSpace G]
    [NonarchimedeanGroup G] [WeaklyLocallyCompactSpace G] :
    (𝓝 (1 : G)).HasBasis (fun H : OpenSubgroup G ↦ IsCompact (H : Set G)) fun H ↦ (H : Set G) :=
  (nhds_one_hasBasis_openSubgroup G).to_hasBasis'
    (fun W _ ↦ exists_openSubgroup_isCompact_subset W.mem_nhds_one)
    fun H _ ↦ H.mem_nhds_one

/-- In a weakly locally compact nonarchimedean group, left cosets of compact open subgroups form a
neighbourhood basis at every point `g : G`. -/
@[to_additive /-- In a weakly locally compact nonarchimedean additive group, left cosets of compact
open additive subgroups form a neighbourhood basis at every point `g : G`. -/]
theorem nhds_hasBasis_isCompact_openSubgroup (g : G) :
    (𝓝 g).HasBasis (fun H : OpenSubgroup G ↦ IsCompact (H : Set G)) fun H ↦ g • (H : Set G) := by
  have h := (nhds_one_hasBasis_isCompact_openSubgroup G).map (Homeomorph.mulLeft g)
  rw [(Homeomorph.mulLeft g).map_nhds_eq 1] at h
  simpa [← Set.image_smul, smul_eq_mul] using h

/-- In a weakly locally compact nonarchimedean group, the compact open subgroups are coinitial in
`OpenSubgroup G` (cofinal under reverse inclusion `≥`). -/
@[to_additive /-- In a weakly locally compact nonarchimedean additive group, the compact open
additive subgroups are coinitial in `OpenAddSubgroup G` (cofinal under reverse inclusion `≥`). -/]
theorem isCoinitial_isCompact_openSubgroup (G : Type*) [Group G] [TopologicalSpace G]
    [NonarchimedeanGroup G] [WeaklyLocallyCompactSpace G] :
    IsCoinitial {V : OpenSubgroup G | IsCompact (V : Set G)} := fun W ↦
  exists_openSubgroup_isCompact_subset W.mem_nhds_one

end NonarchimedeanGroup

namespace IsTopologicalGroup

/-- **Van Dantzig's basis step.** A weakly locally compact zero-dimensional topological group is
nonarchimedean: shrinking any neighbourhood of `1` to a closed compact neighbourhood and refining
by a clopen set produces a compact clopen identity neighbourhood whose left-translation stabilizer
is an open subgroup inside it. Since a locally compact (or compact) totally disconnected
topological group is Hausdorff and therefore zero-dimensional, this instance applies automatically
to every profinite and locally profinite group. -/
@[to_additive /-- **Van Dantzig's basis step.** A weakly locally compact zero-dimensional
topological additive group is nonarchimedean: shrinking any neighbourhood of `0` to a closed
compact neighbourhood and refining by a clopen set produces a compact clopen neighbourhood of `0`
whose translation stabilizer is an open additive subgroup inside it. Since a locally compact (or
compact) totally disconnected topological additive group is Hausdorff and therefore
zero-dimensional, this instance applies automatically to every profinite and locally profinite
additive group. -/]
instance (priority := 100) nonarchimedeanGroup_of_weaklyLocallyCompactSpace {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [WeaklyLocallyCompactSpace G]
    [ZeroDimensionalSpace G] : NonarchimedeanGroup G where
  is_nonarchimedean _ hU := by
    obtain ⟨K, hK_mem, -, hK_compact, -, hKU⟩ :=
      TauCeti.exists_mem_nhds_one_isClosed_isCompact_inv_eq_subset hU
    obtain ⟨C, ⟨hC_clopen, h1C⟩, hCK⟩ := (nhds_basis_isClopen (1 : G)).mem_iff.mp hK_mem
    have hC_compact : IsCompact C := hK_compact.of_isClosed_subset hC_clopen.isClosed hCK
    exact ⟨OpenSubgroup.stabilizer G hC_compact hC_clopen.isOpen,
      (OpenSubgroup.stabilizer_subset hC_compact hC_clopen.isOpen h1C).trans (hCK.trans hKU)⟩

section VanDantzig

/-- A topological group admitting a compact open subgroup (in particular, one in which every
identity neighbourhood contains a compact open subgroup) is locally compact. -/
@[to_additive /-- A topological additive group admitting a compact open additive subgroup (in
particular, one in which every neighbourhood of `0` contains a compact open additive subgroup) is
locally compact. -/]
theorem locallyCompactSpace_of_exists_openSubgroup_isCompact {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (h : ∀ U ∈ 𝓝 (1 : G), ∃ H : OpenSubgroup G, IsCompact (H : Set G) ∧ (H : Set G) ⊆ U) :
    LocallyCompactSpace G := by
  obtain ⟨H, hH_compact, -⟩ := h univ univ_mem
  exact hH_compact.locallyCompactSpace_of_mem_nhds_of_group H.mem_nhds_one

/-- **Van Dantzig's theorem.** For a Hausdorff topological group `G`, the following are equivalent:
1. `G` is locally compact and totally disconnected
   (`LocallyCompactSpace G ∧ TotallyDisconnectedSpace G`);
2. `G` is locally compact and nonarchimedean (`LocallyCompactSpace G ∧ NonarchimedeanGroup G`);
3. every neighbourhood of `1` contains a compact open subgroup;
4. the compact open subgroups form a filter basis of `𝓝 (1 : G)`. -/
@[to_additive /-- **Van Dantzig's theorem (additive).** For a Hausdorff topological additive group
`G`, the following are equivalent:
1. `G` is locally compact and totally disconnected
   (`LocallyCompactSpace G ∧ TotallyDisconnectedSpace G`);
2. `G` is locally compact and nonarchimedean (`LocallyCompactSpace G ∧ NonarchimedeanAddGroup G`);
3. every neighbourhood of `0` contains a compact open additive subgroup;
4. the compact open additive subgroups form a filter basis of `𝓝 (0 : G)`. -/]
theorem locallyCompactSpace_and_totallyDisconnectedSpace_tfae (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] :
    List.TFAE
      [LocallyCompactSpace G ∧ TotallyDisconnectedSpace G,
       LocallyCompactSpace G ∧ NonarchimedeanGroup G,
       ∀ U ∈ 𝓝 (1 : G), ∃ H : OpenSubgroup G, IsCompact (H : Set G) ∧ (H : Set G) ⊆ U,
       (𝓝 (1 : G)).HasBasis (fun H : OpenSubgroup G ↦ IsCompact (H : Set G))
         fun H ↦ (H : Set G)] := by
  tfae_have 1 → 4
  | ⟨hLC, hTD⟩ => NonarchimedeanGroup.nhds_one_hasBasis_isCompact_openSubgroup G
  tfae_have 4 → 3
  | hB => fun U hU ↦ hB.mem_iff.mp hU
  tfae_have 3 → 2
  | h => ⟨locallyCompactSpace_of_exists_openSubgroup_isCompact h,
      { is_nonarchimedean := fun U hU ↦ let ⟨H, _, hHU⟩ := h U hU; ⟨H, hHU⟩ }⟩
  tfae_have 2 → 1
  | ⟨hLC, hNA⟩ => ⟨hLC, inferInstance⟩
  tfae_finish

/-- A Hausdorff topological group is locally compact and totally disconnected if and only if it is
locally compact and nonarchimedean. -/
@[to_additive /-- A Hausdorff topological additive group is locally compact and totally
disconnected if and only if it is locally compact and nonarchimedean. -/]
theorem locallyCompactSpace_and_totallyDisconnectedSpace_iff_nonarchimedeanGroup (G : Type*)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] :
    LocallyCompactSpace G ∧ TotallyDisconnectedSpace G ↔
      LocallyCompactSpace G ∧ NonarchimedeanGroup G :=
  (locallyCompactSpace_and_totallyDisconnectedSpace_tfae G).out 1 2

/-- A Hausdorff topological group is locally compact and totally disconnected if and only if every
neighbourhood of `1` contains a compact open subgroup. -/
@[to_additive /-- A Hausdorff topological additive group is locally compact and totally
disconnected if and only if every neighbourhood of `0` contains a compact open additive
subgroup. -/]
theorem locallyCompactSpace_and_totallyDisconnectedSpace_iff_exists_openSubgroup_isCompact
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] :
    LocallyCompactSpace G ∧ TotallyDisconnectedSpace G ↔
      ∀ U ∈ 𝓝 (1 : G), ∃ H : OpenSubgroup G, IsCompact (H : Set G) ∧ (H : Set G) ⊆ U :=
  (locallyCompactSpace_and_totallyDisconnectedSpace_tfae G).out 1 3

/-- A Hausdorff topological group is locally compact and totally disconnected if and only if the
compact open subgroups form a filter basis of `𝓝 (1 : G)`. -/
@[to_additive /-- A Hausdorff topological additive group is locally compact and totally
disconnected if and only if the compact open additive subgroups form a filter basis of
`𝓝 (0 : G)`. -/]
theorem locallyCompactSpace_and_totallyDisconnectedSpace_iff_nhds_one_hasBasis (G : Type*)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] :
    LocallyCompactSpace G ∧ TotallyDisconnectedSpace G ↔
      (𝓝 (1 : G)).HasBasis (fun H : OpenSubgroup G ↦ IsCompact (H : Set G))
        fun H ↦ (H : Set G) :=
  (locallyCompactSpace_and_totallyDisconnectedSpace_tfae G).out 1 4

end VanDantzig

end IsTopologicalGroup

end
