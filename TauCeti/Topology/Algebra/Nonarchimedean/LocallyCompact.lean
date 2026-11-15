/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Mathlib.Topology.InductiveDimension.Classes
public import Mathlib.Topology.Separation.Regular
public import TauCeti.Topology.Algebra.Nonarchimedean.TotallyDisconnected
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
import TauCeti.Topology.Algebra.Group.OpenSubgroup.Compact
import TauCeti.Topology.Algebra.MulAction.Stabilizer

/-!
# Van Dantzig's theorem and locally profinite groups

A topological group is called *locally profinite* (or an *`ℓ`-group*) when it is locally compact,
Hausdorff, and totally disconnected. Van Dantzig's theorem asserts that these groups are precisely
the Hausdorff topological groups whose identity neighbourhoods admit a basis of compact open
subgroups.

This module proves van Dantzig's theorem in both its typeclass-synthesis form and its equivalence
(`↔` and `List.TFAE`) forms:

* Every weakly locally compact zero-dimensional topological group is nonarchimedean
  (`TauCeti.IsTopologicalGroup.nonarchimedeanGroup_of_weaklyLocallyCompactSpace`), generalizing
  `TauCeti.IsTopologicalGroup.nonarchimedeanGroup_of_compactSpace` from compact groups to locally
  compact ones. Inside a compact closed identity neighbourhood `K` and a prescribed neighbourhood
  `U ∈ 𝓝 1`, zero-dimensionality supplies a clopen identity neighbourhood `C ⊆ U ∩ K`; `C` is
  compact and open, so its left-translation stabilizer `TauCeti.openStabilizer` is an open subgroup
  contained in `C ⊆ U`. Since Mathlib derives `T2Space`, `WeaklyLocallyCompactSpace`, and
  `ZeroDimensionalSpace` automatically from `[IsTopologicalGroup G] [LocallyCompactSpace G]
  [TotallyDisconnectedSpace G]`, typeclass search synthesizes `NonarchimedeanGroup G` directly on
  any locally profinite group.
* In any weakly locally compact nonarchimedean group, intersecting an open subgroup with a compact
  identity neighbourhood upgrades the open-subgroup basis to a basis of *compact* open subgroups,
  both unrestricted (`NonarchimedeanGroup.nhds_one_hasBasis_openSubgroup_isCompact`) and restricted
  below any fixed open subgroup `U₀`
  (`NonarchimedeanGroup.nhds_one_hasBasis_openSubgroup_isCompact_le`).
* For any `T₀` (hence Hausdorff) topological group `G`,
  `TauCeti.tfae_locallyCompactSpace_totallyDisconnectedSpace` establishes the equivalence of:
  1. `LocallyCompactSpace G ∧ TotallyDisconnectedSpace G`,
  2. `LocallyCompactSpace G ∧ ZeroDimensionalSpace G`,
  3. `LocallyCompactSpace G ∧ NonarchimedeanGroup G`,
  4. compact open subgroups form a filter basis of `𝓝 1`, and
  5. every neighbourhood of `1` contains a compact open subgroup.

## Main instances

* `TauCeti.IsTopologicalGroup.nonarchimedeanGroup_of_weaklyLocallyCompactSpace`,
  `TauCeti.IsTopologicalAddGroup.nonarchimedeanAddGroup_of_weaklyLocallyCompactSpace`,
  `TauCeti.IsTopologicalRing.nonarchimedeanRing_of_weaklyLocallyCompactSpace`: weakly locally
  compact zero-dimensional topological groups and rings are nonarchimedean.

## Main results

* `NonarchimedeanGroup.exists_openSubgroup_isCompact_subset`,
  `NonarchimedeanGroup.nhds_one_hasBasis_openSubgroup_isCompact`,
  `NonarchimedeanGroup.nhds_one_hasBasis_openSubgroup_isCompact_le`: compact open subgroups form a
  neighbourhood basis of `1`.
* `TauCeti.locallyCompactSpace_and_totallyDisconnectedSpace_iff_exists_openSubgroup_isCompact`,
  `TauCeti.tfae_locallyCompactSpace_totallyDisconnectedSpace`: **van Dantzig's theorem**.

## References

* D. van Dantzig, *Zur topologischen Algebra. III. Brouwersche und Cantorsche Gruppen*, Compositio
  Math. **3** (1936), 408–426.
* J. Bernstein, *Representations of `p`-adic Groups*, Harvard lecture notes (1992), Ch. I, §1.1.
* L. Kramer, *Locally Profinite Groups and Bruhat–Tits Buildings*, Lemma 1.41, Proposition 1.43,
  and Theorem 1.44.
-/

public section

open Filter Set Topology

namespace NonarchimedeanGroup

variable {G : Type*} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  [WeaklyLocallyCompactSpace G]

/-- In a weakly locally compact nonarchimedean group, every neighbourhood of `1` contains a compact
open subgroup. -/
@[to_additive /-- In a weakly locally compact nonarchimedean additive group, every neighbourhood of
`0` contains a compact open additive subgroup. -/]
theorem exists_openSubgroup_isCompact_subset {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ H : OpenSubgroup G, IsCompact (H : Set G) ∧ (H : Set G) ⊆ U := by
  obtain ⟨K, hK_nhds, hKc, -⟩ := exists_mem_nhds_isCompact_isClosed (1 : G)
  obtain ⟨H, hH⟩ := is_nonarchimedean (U ∩ K) (inter_mem hU hK_nhds)
  exact ⟨H, H.isCompact_of_subset hKc (hH.trans inter_subset_right), hH.trans inter_subset_left⟩

variable (G) in
/-- **Compact open subgroups form a basis of `𝓝 1`** in a weakly locally compact nonarchimedean
group. -/
@[to_additive /-- **Compact open additive subgroups form a basis of `𝓝 0`** in a weakly locally
compact nonarchimedean additive group. -/]
theorem nhds_one_hasBasis_openSubgroup_isCompact :
    (𝓝 (1 : G)).HasBasis (fun H : OpenSubgroup G ↦ IsCompact (H : Set G)) fun H ↦ (H : Set G) :=
  ⟨fun _ ↦ ⟨fun hU ↦ exists_openSubgroup_isCompact_subset hU,
    fun ⟨H, _, hHU⟩ ↦ mem_of_superset H.mem_nhds_one hHU⟩⟩

/-- In a weakly locally compact nonarchimedean group, the compact open subgroups contained in a
given open subgroup `U₀` form a basis of `𝓝 1` (`U₀` itself need not be compact). -/
@[to_additive /-- In a weakly locally compact nonarchimedean additive group, the compact open
additive subgroups contained in a given open additive subgroup `U₀` form a basis of `𝓝 0` (`U₀`
itself need not be compact). -/]
theorem nhds_one_hasBasis_openSubgroup_isCompact_le (U₀ : OpenSubgroup G) :
    (𝓝 (1 : G)).HasBasis (fun H : OpenSubgroup G ↦ IsCompact (H : Set G) ∧ H ≤ U₀)
      fun H ↦ (H : Set G) := by
  refine ⟨fun U ↦ ⟨fun hU ↦ ?_, fun ⟨H, _, hHU⟩ ↦ mem_of_superset H.mem_nhds_one hHU⟩⟩
  obtain ⟨H, hHc, hHU⟩ := exists_openSubgroup_isCompact_subset (inter_mem hU U₀.mem_nhds_one)
  exact ⟨H, ⟨hHc, hHU.trans inter_subset_right⟩, hHU.trans inter_subset_left⟩

end NonarchimedeanGroup

namespace TauCeti

/-- **Van Dantzig's theorem (instance form).** A weakly locally compact zero-dimensional
topological group is nonarchimedean: every neighbourhood of the identity contains an open subgroup
(in fact a compact open subgroup, via `TauCeti.openStabilizer`). This covers all locally profinite
groups (`[LocallyCompactSpace G] [TotallyDisconnectedSpace G]`), which Mathlib equips with
`T2Space` and `ZeroDimensionalSpace` automatically. -/
@[to_additive IsTopologicalAddGroup.nonarchimedeanAddGroup_of_weaklyLocallyCompactSpace
/-- **Van Dantzig's theorem (additive instance form).** A weakly locally compact zero-dimensional
topological additive group is nonarchimedean: every neighbourhood of zero contains an open additive
subgroup. -/]
instance (priority := 100) IsTopologicalGroup.nonarchimedeanGroup_of_weaklyLocallyCompactSpace
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [WeaklyLocallyCompactSpace G] [ZeroDimensionalSpace G] :
    NonarchimedeanGroup G where
  is_nonarchimedean U hU := by
    obtain ⟨K, hK_nhds, hKc, -⟩ := exists_mem_nhds_isCompact_isClosed (1 : G)
    obtain ⟨C, ⟨hC, h1C⟩, hCUK⟩ := (nhds_basis_isClopen (1 : G)).mem_iff.mp (inter_mem hU hK_nhds)
    have hCc : IsCompact C := hKc.of_isClosed_subset hC.isClosed (hCUK.trans inter_subset_right)
    exact ⟨openStabilizer G C hCc hC.isOpen,
      (openStabilizer_subset_of_one_mem hCc hC.isOpen h1C).trans (hCUK.trans inter_subset_left)⟩

/-- A weakly locally compact zero-dimensional topological ring is a nonarchimedean ring. -/
instance (priority := 100) IsTopologicalRing.nonarchimedeanRing_of_weaklyLocallyCompactSpace
    {R : Type*} [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    [WeaklyLocallyCompactSpace R] [ZeroDimensionalSpace R] :
    NonarchimedeanRing R where
  is_nonarchimedean := (inferInstance : NonarchimedeanAddGroup R).is_nonarchimedean

section Equivalences

/-- Compact open subgroups form a filter basis of `𝓝 1` if and only if every neighbourhood of `1`
contains a compact open subgroup. -/
@[to_additive /-- Compact open additive subgroups form a filter basis of `𝓝 0` if and only if every
neighbourhood of `0` contains a compact open additive subgroup. -/]
theorem nhds_one_hasBasis_openSubgroup_isCompact_iff (G : Type*) [Group G] [TopologicalSpace G] :
    ((𝓝 (1 : G)).HasBasis (fun H : OpenSubgroup G ↦ IsCompact (H : Set G)) fun H ↦ (H : Set G)) ↔
      ∀ U ∈ 𝓝 (1 : G), ∃ H : OpenSubgroup G, IsCompact (H : Set G) ∧ (H : Set G) ⊆ U :=
  ⟨fun h _ hU ↦ h.mem_iff.mp hU,
    fun h ↦ ⟨fun _ ↦ ⟨fun hU ↦ h _ hU, fun ⟨H, _, hHU⟩ ↦ mem_of_superset H.mem_nhds_one hHU⟩⟩⟩

/-- A topological group is locally compact and nonarchimedean if and only if every neighbourhood of
`1` contains a compact open subgroup. No separation axiom is needed. -/
@[to_additive /-- A topological additive group is locally compact and nonarchimedean if and only if
every neighbourhood of `0` contains a compact open additive subgroup. No separation axiom is
needed. -/]
theorem locallyCompactSpace_and_nonarchimedeanGroup_iff_exists_openSubgroup_isCompact (G : Type*)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    (LocallyCompactSpace G ∧ NonarchimedeanGroup G) ↔
      ∀ U ∈ 𝓝 (1 : G), ∃ H : OpenSubgroup G, IsCompact (H : Set G) ∧ (H : Set G) ⊆ U := by
  constructor
  · rintro ⟨_, _⟩ _ hU
    exact NonarchimedeanGroup.exists_openSubgroup_isCompact_subset hU
  · intro h
    obtain ⟨H, hHc, -⟩ := h univ univ_mem
    exact ⟨hHc.locallyCompactSpace_of_mem_nhds_of_group H.mem_nhds_one,
      ⟨fun U hU ↦ (h U hU).imp fun _ hH ↦ hH.2⟩⟩

/-- A topological group is locally compact and zero-dimensional if and only if it is locally
compact and nonarchimedean. No separation axiom is needed. -/
@[to_additive /-- A topological additive group is locally compact and zero-dimensional if and only
if it is locally compact and nonarchimedean. No separation axiom is needed. -/]
theorem locallyCompactSpace_and_zeroDimensionalSpace_iff_nonarchimedeanGroup (G : Type*)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    (LocallyCompactSpace G ∧ ZeroDimensionalSpace G) ↔
      (LocallyCompactSpace G ∧ NonarchimedeanGroup G) :=
  ⟨fun ⟨_, _⟩ ↦ ⟨‹_›, inferInstance⟩,
    fun ⟨_, _⟩ ↦ ⟨‹_›, NonarchimedeanGroup.zeroDimensionalSpace G⟩⟩

/-- In a weakly locally compact `T₀` (hence Hausdorff) topological group, total disconnectedness is
equivalent to being nonarchimedean. -/
@[to_additive /-- In a weakly locally compact `T₀` (hence Hausdorff) topological additive group,
total disconnectedness is equivalent to being nonarchimedean. -/]
theorem totallyDisconnectedSpace_iff_nonarchimedeanGroup (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T0Space G] [WeaklyLocallyCompactSpace G] :
    TotallyDisconnectedSpace G ↔ NonarchimedeanGroup G :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

/-- A `T₀` (hence Hausdorff) topological group is locally compact and totally disconnected if and
only if it is locally compact and nonarchimedean. -/
@[to_additive /-- A `T₀` (hence Hausdorff) topological additive group is locally compact and
totally disconnected if and only if it is locally compact and nonarchimedean. -/]
theorem locallyCompactSpace_and_totallyDisconnectedSpace_iff_nonarchimedeanGroup (G : Type*)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T0Space G] :
    (LocallyCompactSpace G ∧ TotallyDisconnectedSpace G) ↔
      (LocallyCompactSpace G ∧ NonarchimedeanGroup G) :=
  and_congr_right fun _ ↦ totallyDisconnectedSpace_iff_nonarchimedeanGroup G

/-- **Van Dantzig's theorem.** A `T₀` (hence Hausdorff) topological group is locally compact and
totally disconnected if and only if every neighbourhood of `1` contains a compact open subgroup. -/
@[to_additive /-- **Van Dantzig's theorem (additive form).** A `T₀` (hence Hausdorff) topological
additive group is locally compact and totally disconnected if and only if every neighbourhood of `0`
contains a compact open additive subgroup. -/]
theorem locallyCompactSpace_and_totallyDisconnectedSpace_iff_exists_openSubgroup_isCompact
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T0Space G] :
    (LocallyCompactSpace G ∧ TotallyDisconnectedSpace G) ↔
      ∀ U ∈ 𝓝 (1 : G), ∃ H : OpenSubgroup G, IsCompact (H : Set G) ∧ (H : Set G) ⊆ U :=
  (locallyCompactSpace_and_totallyDisconnectedSpace_iff_nonarchimedeanGroup G).trans
    (locallyCompactSpace_and_nonarchimedeanGroup_iff_exists_openSubgroup_isCompact G)

/-- **Van Dantzig's theorem (`List.TFAE` form).** For a `T₀` (hence Hausdorff) topological group
`G`, the following are equivalent:
1. `G` is locally compact and totally disconnected (locally profinite);
2. `G` is locally compact and zero-dimensional;
3. `G` is locally compact and nonarchimedean;
4. compact open subgroups form a filter basis of `𝓝 1`;
5. every neighbourhood of `1` contains a compact open subgroup. -/
@[to_additive tfae_locallyCompactSpace_totallyDisconnectedSpace_add
/-- **Van Dantzig's theorem (additive `List.TFAE` form).** For a `T₀` (hence Hausdorff) topological
additive group `G`, the following are equivalent:
1. `G` is locally compact and totally disconnected;
2. `G` is locally compact and zero-dimensional;
3. `G` is locally compact and nonarchimedean;
4. compact open additive subgroups form a filter basis of `𝓝 0`;
5. every neighbourhood of `0` contains a compact open additive subgroup. -/]
theorem tfae_locallyCompactSpace_totallyDisconnectedSpace (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T0Space G] :
    List.TFAE
      [ LocallyCompactSpace G ∧ TotallyDisconnectedSpace G,
        LocallyCompactSpace G ∧ ZeroDimensionalSpace G,
        LocallyCompactSpace G ∧ NonarchimedeanGroup G,
        (𝓝 (1 : G)).HasBasis (fun H : OpenSubgroup G ↦ IsCompact (H : Set G)) fun H ↦ (H : Set G),
        ∀ U ∈ 𝓝 (1 : G), ∃ H : OpenSubgroup G, IsCompact (H : Set G) ∧ (H : Set G) ⊆ U ] := by
  tfae_have 1 ↔ 3 := locallyCompactSpace_and_totallyDisconnectedSpace_iff_nonarchimedeanGroup G
  tfae_have 2 ↔ 3 := locallyCompactSpace_and_zeroDimensionalSpace_iff_nonarchimedeanGroup G
  tfae_have 3 ↔ 5 :=
    locallyCompactSpace_and_nonarchimedeanGroup_iff_exists_openSubgroup_isCompact G
  tfae_have 4 ↔ 5 := nhds_one_hasBasis_openSubgroup_isCompact_iff G
  tfae_finish

end Equivalences

end TauCeti
