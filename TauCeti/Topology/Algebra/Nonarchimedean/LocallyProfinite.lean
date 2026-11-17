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
import TauCeti.Topology.Algebra.MulAction.Stabilizer

/-!
# Van Dantzig's theorem and locally profinite groups

A Hausdorff topological group `G` is *locally profinite* (an *l-group*) if every neighbourhood of
the identity contains a compact open subgroup. Van Dantzig's theorem identifies the locally
profinite groups among Hausdorff topological groups by three equivalent conditions:

1. `G` is locally compact and totally disconnected (`LocallyCompactSpace G` and
   `TotallyDisconnectedSpace G`);
2. `G` is locally compact and nonarchimedean (`LocallyCompactSpace G` and `NonarchimedeanGroup G`);
3. every neighbourhood of `1` contains a compact open subgroup.

Mathlib's `IsTopologicalGroup.exist_openSubgroup_sub_clopen_nhds_of_one` constructs open subgroups
inside clopen neighbourhoods of `1` only when the ambient group `G` is compact. In any weakly
locally compact zero-dimensional topological group (and hence in every locally profinite group),
the clopen basis at `1` inside a compact neighbourhood supplies a compact clopen neighbourhood `C`
of `1` inside any given neighbourhood of `1`, whose left translation stabilizer
(`IsCompact.stabilizerOpenSubgroup` from `TauCeti.Topology.Algebra.MulAction.Stabilizer`) is a
compact open subgroup contained in `C`.

Consequences recorded here include:
* `NonarchimedeanGroup G` synthesizes automatically for weakly locally compact zero-dimensional
  topological groups (`TauCeti.nonarchimedeanGroup_of_locallyCompactSpace`), and in particular for
  locally compact totally disconnected topological groups;
* the compact open subgroups form a filter basis of `𝓝 1`
  (`TauCeti.nhds_one_hasBasis_isCompact_openSubgroup`), and those contained in a given open
  subgroup `U₀` form a cofinal filter basis (`OpenSubgroup.nhds_one_hasBasis_isCompact_le`,
  `OpenSubgroup.exists_isCompact_le`), complementing downward directedness in
  `TauCeti.Topology.Algebra.Group.OpenSubgroup.Basic`.

Every result carries `@[to_additive]` so additive groups such as `ℚ_[p]` and local fields inherit
the corresponding compact open additive subgroup basis.

## Main results

* `TauCeti.exists_isCompact_openSubgroup_subset`,
  `TauCeti.nonarchimedeanGroup_of_locallyCompactSpace`, and
  `TauCeti.nhds_one_hasBasis_isCompact_openSubgroup`: compact open subgroups form a basis of `𝓝 1`
  in any weakly locally compact zero-dimensional topological group.
* `OpenSubgroup.nhds_one_hasBasis_isCompact_le` and `OpenSubgroup.exists_isCompact_le`:
  cofinality of compact open subgroups inside a given open subgroup.
* `TauCeti.locallyCompactSpace_and_nonarchimedeanGroup_iff_exists_isCompact_openSubgroup_subset`,
  `TauCeti.locallyCompactSpace_and_nonarchimedeanGroup_tfae`, and
  `TauCeti.totallyDisconnectedSpace_iff_nonarchimedeanGroup` (with
  `locallyCompactSpace_and_totallyDisconnectedSpace_iff_exists_isCompact_openSubgroup_subset`):
  van Dantzig's equivalence theorem.

## References

* J. Bernstein, *Representations of p-adic Groups* (Harvard lecture notes by K. E. Rumelhart,
  1992), Chapter I, Section 1.1, Definition 1, p. 7.
* L. Kramer, *Locally Compact Groups and Lie Groups*, Chapter 1 (version of 19 May 2020),
  Lemma 1.41, Proposition 1.43, and Theorem 1.44, pp. 17–19,
  <https://www.uni-muenster.de/AGKramer/content/ch1.pdf>.
-/

public section

open Filter Set Topology

namespace TauCeti

section LocallyProfinite

variable {G : Type*} [Group G] [TopologicalSpace G]

section ZeroDimensional

variable [IsTopologicalGroup G]

/-- **Van Dantzig's theorem (existence form).** In a weakly locally compact zero-dimensional
topological group (in particular, any locally profinite group), every identity neighbourhood
contains a compact open subgroup. -/
@[to_additive
/-- **Van Dantzig's theorem (additive existence form).** In a weakly locally compact
zero-dimensional topological additive group, every neighbourhood of `0` contains a compact open
additive subgroup. -/]
theorem exists_isCompact_openSubgroup_subset [WeaklyLocallyCompactSpace G]
    [ZeroDimensionalSpace G] {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ H : OpenSubgroup G, IsCompact (H : Set G) ∧ (H : Set G) ⊆ U := by
  obtain ⟨K, hK_cpt, hK_nhds⟩ := exists_compact_mem_nhds (1 : G)
  obtain ⟨C, ⟨hC_clopen, h1C⟩, hCUK⟩ :=
    (nhds_basis_isClopen (1 : G)).mem_iff.mp (inter_mem hU hK_nhds)
  have hC_cpt : IsCompact C :=
    hK_cpt.of_isClosed_subset hC_clopen.isClosed (hCUK.trans inter_subset_right)
  exact ⟨hC_cpt.stabilizerOpenSubgroup G hC_clopen.isOpen,
    hC_cpt.isCompact_stabilizerOpenSubgroup hC_clopen.isOpen h1C,
    (hC_cpt.stabilizerOpenSubgroup_subset hC_clopen.isOpen h1C).trans
      (hCUK.trans inter_subset_left)⟩

/-- A weakly locally compact zero-dimensional topological group (and hence any locally profinite
group) is nonarchimedean. -/
@[to_additive
/-- A weakly locally compact zero-dimensional topological additive group is nonarchimedean. -/]
instance (priority := 100) nonarchimedeanGroup_of_locallyCompactSpace [WeaklyLocallyCompactSpace G]
    [ZeroDimensionalSpace G] : NonarchimedeanGroup G where
  is_nonarchimedean _ hU :=
    let ⟨H, _, hHU⟩ := exists_isCompact_openSubgroup_subset hU
    ⟨H, hHU⟩

/-- **Compact open subgroups form a basis of `𝓝 1`.** In a weakly locally compact zero-dimensional
topological group (in particular, any locally profinite group), the compact open subgroups form a
filter basis of the identity neighbourhood filter. -/
@[to_additive
/-- **Compact open additive subgroups form a basis of `𝓝 0`.** In a weakly locally compact
zero-dimensional topological additive group, the compact open additive subgroups form a filter basis
of the neighbourhoods of `0`. -/]
theorem nhds_one_hasBasis_isCompact_openSubgroup [WeaklyLocallyCompactSpace G]
    [ZeroDimensionalSpace G] :
    (𝓝 (1 : G)).HasBasis (fun H : OpenSubgroup G ↦ IsCompact (H : Set G))
      fun H ↦ (H : Set G) :=
  ⟨fun _ ↦ ⟨exists_isCompact_openSubgroup_subset,
    fun ⟨H, _, hH⟩ ↦ mem_of_superset H.mem_nhds_one hH⟩⟩

/-- A topological group is locally compact and nonarchimedean if and only if every identity
neighbourhood contains a compact open subgroup. Hausdorffness of `G` is not required. -/
@[to_additive
/-- A topological additive group is locally compact and nonarchimedean if and only if every
neighbourhood of `0` contains a compact open additive subgroup. Hausdorffness of `G` is not
required. -/]
theorem locallyCompactSpace_and_nonarchimedeanGroup_iff_exists_isCompact_openSubgroup_subset :
    LocallyCompactSpace G ∧ NonarchimedeanGroup G ↔
      ∀ U ∈ 𝓝 (1 : G), ∃ H : OpenSubgroup G, IsCompact (H : Set G) ∧ (H : Set G) ⊆ U := by
  refine ⟨fun ⟨_, _⟩ U hU ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨K, hK_nhds, hKU, hK_cpt⟩ := local_compact_nhds hU
    obtain ⟨H, hHK⟩ := NonarchimedeanGroup.is_nonarchimedean K hK_nhds
    exact ⟨H, H.isCompact_of_subset hK_cpt hHK, hHK.trans hKU⟩
  · obtain ⟨H, hHcpt, -⟩ := h univ univ_mem
    exact ⟨hHcpt.locallyCompactSpace_of_mem_nhds_of_group H.mem_nhds_one,
      ⟨fun U hU ↦ let ⟨K, _, hKU⟩ := h U hU; ⟨K, hKU⟩⟩⟩

end ZeroDimensional

section VanDantzig

variable [IsTopologicalGroup G] [T2Space G]

variable (G) in
/-- **Van Dantzig's theorem.** For a Hausdorff topological group `G`, the following are equivalent:
1. `G` is locally compact and totally disconnected;
2. `G` is locally compact and `NonarchimedeanGroup` (every neighbourhood of `1` contains an open
   subgroup);
3. every neighbourhood of `1` contains a compact open subgroup. -/
@[to_additive
/-- **Van Dantzig's theorem (additive form).** For a Hausdorff topological additive group `G`, the
following are equivalent:
1. `G` is locally compact and totally disconnected;
2. `G` is locally compact and `NonarchimedeanAddGroup` (every neighbourhood of `0` contains an open
   additive subgroup);
3. every neighbourhood of `0` contains a compact open additive subgroup. -/]
theorem locallyCompactSpace_and_nonarchimedeanGroup_tfae :
    List.TFAE
      [LocallyCompactSpace G ∧ TotallyDisconnectedSpace G,
       LocallyCompactSpace G ∧ NonarchimedeanGroup G,
       ∀ U ∈ 𝓝 (1 : G), ∃ H : OpenSubgroup G, IsCompact (H : Set G) ∧ (H : Set G) ⊆ U] := by
  tfae_have 1 → 3 := fun ⟨_, _⟩ _ hU ↦ exists_isCompact_openSubgroup_subset hU
  tfae_have 3 → 2 :=
    locallyCompactSpace_and_nonarchimedeanGroup_iff_exists_isCompact_openSubgroup_subset.mpr
  tfae_have 2 → 1 := fun ⟨hLC, _⟩ ↦ ⟨hLC, inferInstance⟩
  tfae_finish

/-- A Hausdorff topological group is locally compact and totally disconnected if and only if every
identity neighbourhood contains a compact open subgroup. -/
@[to_additive
/-- A Hausdorff topological additive group is locally compact and totally disconnected if and only
if every neighbourhood of `0` contains a compact open additive subgroup. -/]
theorem locallyCompactSpace_and_totallyDisconnectedSpace_iff_exists_isCompact_openSubgroup_subset :
    LocallyCompactSpace G ∧ TotallyDisconnectedSpace G ↔
      ∀ U ∈ 𝓝 (1 : G), ∃ H : OpenSubgroup G, IsCompact (H : Set G) ∧ (H : Set G) ⊆ U :=
  (locallyCompactSpace_and_nonarchimedeanGroup_tfae G).out 1 3

/-- A weakly locally compact Hausdorff topological group is totally disconnected if and only if it
is nonarchimedean. -/
@[to_additive
/-- A weakly locally compact Hausdorff topological additive group is totally disconnected if and
only if it is nonarchimedean. -/]
theorem totallyDisconnectedSpace_iff_nonarchimedeanGroup [WeaklyLocallyCompactSpace G] :
    TotallyDisconnectedSpace G ↔ NonarchimedeanGroup G :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

end VanDantzig

end LocallyProfinite

end TauCeti

namespace OpenSubgroup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [WeaklyLocallyCompactSpace G] [ZeroDimensionalSpace G]

/-- **Cofinality of compact open subgroups inside a given open subgroup.** In a weakly locally
compact zero-dimensional topological group (in particular, any locally profinite group), the compact
open subgroups contained in a fixed open subgroup `U₀` form a filter basis of `𝓝 1`. -/
@[to_additive
/-- In a weakly locally compact zero-dimensional topological additive group, the compact open
additive subgroups contained in a fixed open additive subgroup `U₀` form a filter basis of
`𝓝 0`. -/]
theorem nhds_one_hasBasis_isCompact_le (U₀ : OpenSubgroup G) :
    (𝓝 (1 : G)).HasBasis (fun H : OpenSubgroup G ↦ IsCompact (H : Set G) ∧ H ≤ U₀)
      fun H ↦ (H : Set G) := by
  refine ⟨fun W ↦ ⟨fun hW ↦ ?_, fun ⟨H, _, hHW⟩ ↦ mem_of_superset H.mem_nhds_one hHW⟩⟩
  obtain ⟨H, hHcpt, hH⟩ :=
    TauCeti.exists_isCompact_openSubgroup_subset (inter_mem hW U₀.mem_nhds_one)
  exact ⟨H, ⟨hHcpt, hH.trans inter_subset_right⟩, hH.trans inter_subset_left⟩

/-- Every open subgroup of a weakly locally compact zero-dimensional topological group (in
particular, any locally profinite group) contains a compact open subgroup. -/
@[to_additive
/-- Every open additive subgroup of a weakly locally compact zero-dimensional topological additive
group contains a compact open additive subgroup. -/]
theorem exists_isCompact_le (U₀ : OpenSubgroup G) :
    ∃ H : OpenSubgroup G, IsCompact (H : Set G) ∧ H ≤ U₀ := by
  obtain ⟨H, hHcpt, hH⟩ := TauCeti.exists_isCompact_openSubgroup_subset U₀.mem_nhds_one
  exact ⟨H, hHcpt, hH⟩

end OpenSubgroup
