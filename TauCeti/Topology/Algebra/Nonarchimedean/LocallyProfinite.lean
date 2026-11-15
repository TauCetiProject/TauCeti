/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.TFAE
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
public import Mathlib.Topology.Separation.Regular
public import TauCeti.Topology.Algebra.Group.OpenSubgroup.Basic
public import TauCeti.Topology.Algebra.Group.Separation
import TauCeti.Topology.Algebra.Group.Pointwise

/-!
# Van Dantzig's theorem and locally profinite groups

A Hausdorff topological group `G` is *locally profinite* (an *`ℓ`-group*) when it is locally
compact and totally disconnected. Van Dantzig's theorem shows that this topological condition is
equivalent both to being locally compact and `NonarchimedeanGroup` (every identity neighbourhood
contains an open subgroup) and to having a neighbourhood basis at `1` consisting of compact open
subgroups.

In a weakly locally compact zero-dimensional topological group (which includes every locally
compact totally disconnected topological group, since `TotallyDisconnectedSpace` implies `T₁` and
topological groups are completely regular), every identity neighbourhood contains a compact clopen
identity neighbourhood `C`, and its left translation stabilizer `MulAction.stabilizerOpenSubgroup`
(from `TauCeti.Topology.Algebra.Group.Pointwise`) is an open subgroup contained in `C`.
This registers `NonarchimedeanGroup G` as a typeclass instance, generalizing the compact case in
`TauCeti.Topology.Algebra.Nonarchimedean.Profinite`.

Once `G` is weakly locally compact and nonarchimedean, intersecting any identity neighbourhood
with a compact identity neighbourhood produces a basis of compact open subgroups at `1`, and those
contained in a fixed open subgroup `U₀` form a nonempty cofinal downward-directed family (directed
under reverse inclusion via `⊓`). Compact totally disconnected open subgroups are bundled as
objects of `ProfiniteGrp` in `TauCeti.Topology.Algebra.Group.OpenSubgroup.Profinite`.

## Main results

* `IsTopologicalGroup.nonarchimedeanGroup_of_weaklyLocallyCompactSpace`: a weakly locally compact
  zero-dimensional topological group is nonarchimedean; in particular every locally compact totally
  disconnected topological group is automatically an instance of `NonarchimedeanGroup`.
* `NonarchimedeanGroup.nhds_one_hasBasis_isCompact_openSubgroup` and
  `NonarchimedeanGroup.nhds_one_hasBasis_isCompact_openSubgroup_le`: compact open subgroups (and
  those contained in a fixed `U₀ : OpenSubgroup G`) form a basis of `𝓝 1`.
* `NonarchimedeanGroup.isCoinitial_isCompact_openSubgroup_le` and
  `NonarchimedeanGroup.exists_isCompact_openSubgroup_le_inf`: compact open subgroups below `U₀`
  form a coinitial (cofinal under reverse inclusion) family in `OpenSubgroup G`, downward-directed
  by `OpenSubgroup.directedOn_isCompact_le`.
* `IsTopologicalGroup.vanDantzig_tfae`,
  `IsTopologicalGroup.locallyCompactSpace_and_totallyDisconnectedSpace_iff`, and
  `IsTopologicalGroup.totallyDisconnectedSpace_iff_nonarchimedeanGroup`: Van Dantzig's equivalence
  for `T₀` (hence Hausdorff) topological groups, with additive counterparts.

## References

* D. van Dantzig, *Zur topologischen Algebra. III. Brouwersche und Cantorsche Gruppen*,
  Compositio Math. 3 (1936), 408–426.
* J. Bernstein, *Representations of `p`-adic Groups* (notes by K. E. Rumelhart, Harvard, 1992),
  Chapter I, §1.1, Definition 1, p. 7.
* L. Kramer, *Locally Compact Groups*, Lemma 1.41, Proposition 1.43, and Theorem 1.44, pp. 17–19.
-/

public section

open Filter Set
open scoped Topology

/-! ### Nonarchimedean structure and compact-open neighbourhood bases -/

namespace IsTopologicalGroup

section ZeroDimensional

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [WeaklyLocallyCompactSpace G] [ZeroDimensionalSpace G]

/-- A weakly locally compact zero-dimensional topological group is nonarchimedean. Because a
locally compact totally disconnected topological group is Hausdorff and hence zero-dimensional,
typeclass search synthesizes `NonarchimedeanGroup G` automatically for locally profinite groups. -/
@[to_additive /-- A weakly locally compact zero-dimensional topological additive group is
nonarchimedean. Because a locally compact totally disconnected topological additive group is
Hausdorff and hence zero-dimensional, typeclass search synthesizes `NonarchimedeanAddGroup G`
automatically for locally profinite additive groups. -/]
instance (priority := 100) nonarchimedeanGroup_of_weaklyLocallyCompactSpace :
    NonarchimedeanGroup G where
  is_nonarchimedean U hU := by
    obtain ⟨L, hL, hL1⟩ := exists_compact_mem_nhds (1 : G)
    obtain ⟨C, ⟨hC_clopen, h1C⟩, hCU⟩ :=
      (nhds_basis_isClopen (1 : G)).mem_iff.mp (inter_mem hU (interior_mem_nhds.mpr hL1))
    have hC_comp : IsCompact C :=
      hL.of_isClosed_subset hC_clopen.isClosed ((subset_inter_iff.mp hCU).2.trans interior_subset)
    exact ⟨MulAction.stabilizerOpenSubgroup hC_comp hC_clopen.isOpen,
      (MulAction.coe_stabilizerOpenSubgroup_subset hC_comp hC_clopen.isOpen h1C).trans
        (subset_inter_iff.mp hCU).1⟩

end ZeroDimensional

end IsTopologicalGroup

namespace NonarchimedeanGroup

variable {G : Type*} [Group G] [TopologicalSpace G] [WeaklyLocallyCompactSpace G]
  [NonarchimedeanGroup G]

/-- In a weakly locally compact nonarchimedean group (in particular, in any locally profinite
group), every identity neighbourhood contains a compact open subgroup. -/
@[to_additive /-- In a weakly locally compact nonarchimedean additive group (in particular, in any
locally profinite additive group), every neighbourhood of `0` contains a compact open additive
subgroup. -/]
theorem exists_isCompact_openSubgroup_subset {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ U := by
  obtain ⟨L, hL, hL1⟩ := exists_compact_mem_nhds (1 : G)
  obtain ⟨K, hK⟩ := is_nonarchimedean (U ∩ L) (inter_mem hU hL1)
  exact ⟨K, K.isCompact_of_subset hL (subset_inter_iff.mp hK).2, (subset_inter_iff.mp hK).1⟩

variable (G) in
/-- **Compact open subgroups form a basis of `𝓝 1`** in any weakly locally compact nonarchimedean
group (and hence in any locally compact totally disconnected group). -/
@[to_additive /-- **Compact open additive subgroups form a basis of `𝓝 0`** in any weakly locally
compact nonarchimedean additive group (and hence in any locally compact totally disconnected
additive group). -/]
theorem nhds_one_hasBasis_isCompact_openSubgroup :
    (𝓝 (1 : G)).HasBasis (fun K : OpenSubgroup G ↦ IsCompact (K : Set G)) fun K ↦ (K : Set G) :=
  ⟨fun _ ↦ ⟨exists_isCompact_openSubgroup_subset,
    fun ⟨K, _, hK⟩ ↦ mem_of_superset K.mem_nhds_one hK⟩⟩

/-- Compact open subgroups contained in a fixed open subgroup `U₀` form a basis of `𝓝 1`. -/
@[to_additive /-- Compact open additive subgroups contained in a fixed open additive subgroup `U₀`
form a basis of `𝓝 0`. -/]
theorem nhds_one_hasBasis_isCompact_openSubgroup_le (U₀ : OpenSubgroup G) :
    (𝓝 (1 : G)).HasBasis (fun K : OpenSubgroup G ↦ IsCompact (K : Set G) ∧ K ≤ U₀)
      fun K ↦ (K : Set G) :=
  ⟨fun U ↦ ⟨fun hU ↦ by
      obtain ⟨K, hK, hKU⟩ := exists_isCompact_openSubgroup_subset (inter_mem hU U₀.mem_nhds_one)
      exact ⟨K, ⟨hK, (subset_inter_iff.mp hKU).2⟩, (subset_inter_iff.mp hKU).1⟩,
    fun ⟨K, _, hK⟩ ↦ mem_of_superset K.mem_nhds_one hK⟩⟩

/-- Every open subgroup of a weakly locally compact nonarchimedean group contains a compact open
subgroup. -/
@[to_additive /-- Every open additive subgroup of a weakly locally compact nonarchimedean additive
group contains a compact open additive subgroup. -/]
theorem exists_isCompact_openSubgroup_le (U₀ : OpenSubgroup G) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ K ≤ U₀ := by
  obtain ⟨K, hK, hKU₀⟩ := exists_isCompact_openSubgroup_subset U₀.mem_nhds_one
  exact ⟨K, hK, hKU₀⟩

/-- **Cofinality under reverse inclusion:** for any open subgroups `U₀` and `V`, there is a compact
open subgroup `K ≤ U₀` contained in `V`. -/
@[to_additive /-- **Cofinality under reverse inclusion:** for any open additive subgroups `U₀` and
`V`, there is a compact open additive subgroup `K ≤ U₀` contained in `V`. -/]
theorem exists_isCompact_openSubgroup_le_inf (U₀ V : OpenSubgroup G) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ K ≤ U₀ ∧ K ≤ V := by
  obtain ⟨K, hK, hKle⟩ := exists_isCompact_openSubgroup_le (U₀ ⊓ V)
  exact ⟨K, hK, hKle.trans inf_le_left, hKle.trans inf_le_right⟩

/-- The compact open subgroups contained in `U₀` form a coinitial set in `OpenSubgroup G` (that is,
a cofinal family under reverse inclusion `≥`). -/
@[to_additive /-- The compact open additive subgroups contained in `U₀` form a coinitial set in
`OpenAddSubgroup G` (that is, a cofinal family under reverse inclusion `≥`). -/]
theorem isCoinitial_isCompact_openSubgroup_le (U₀ : OpenSubgroup G) :
    IsCoinitial {K : OpenSubgroup G | IsCompact (K : Set G) ∧ K ≤ U₀} := fun V ↦
  let ⟨K, hK, hKU₀, hKV⟩ := exists_isCompact_openSubgroup_le_inf U₀ V
  ⟨K, ⟨hK, hKU₀⟩, hKV⟩

end NonarchimedeanGroup

/-! ### Van Dantzig's theorem -/

namespace IsTopologicalGroup

section NoSeparation

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A topological group admitting at least one compact open subgroup is locally compact. -/
@[to_additive /-- A topological additive group admitting at least one compact open additive
subgroup is locally compact. -/]
theorem locallyCompactSpace_of_exists_isCompact_openSubgroup
    (h : ∃ K : OpenSubgroup G, IsCompact (K : Set G)) : LocallyCompactSpace G :=
  let ⟨K, hK⟩ := h
  hK.locallyCompactSpace_of_mem_nhds_of_group K.mem_nhds_one

/-- Without any separation axiom, a topological group is locally compact and nonarchimedean if and
only if every neighbourhood of `1` contains a compact open subgroup. -/
@[to_additive /-- Without any separation axiom, a topological additive group is locally compact and
nonarchimedean if and only if every neighbourhood of `0` contains a compact open additive
subgroup. -/]
theorem locallyCompactSpace_and_nonarchimedeanGroup_iff :
    LocallyCompactSpace G ∧ NonarchimedeanGroup G ↔
      ∀ U ∈ 𝓝 (1 : G), ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ U := by
  refine ⟨fun ⟨_, _⟩ _ hU ↦ NonarchimedeanGroup.exists_isCompact_openSubgroup_subset hU,
    fun h ↦ ?_⟩
  obtain ⟨K₀, hK₀, -⟩ := h univ univ_mem
  exact ⟨locallyCompactSpace_of_exists_isCompact_openSubgroup ⟨K₀, hK₀⟩,
    { is_nonarchimedean := fun U hU ↦ let ⟨K, _, hKU⟩ := h U hU; ⟨K, hKU⟩ }⟩

end NoSeparation

section T0

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T0Space G]

/-- **Van Dantzig's theorem.** For a `T₀` (equivalently, Hausdorff) topological group `G`, the
following are equivalent:
1. `G` is locally compact and totally disconnected
   (`LocallyCompactSpace G ∧ TotallyDisconnectedSpace G`);
2. `G` is locally compact and nonarchimedean
   (`LocallyCompactSpace G ∧ NonarchimedeanGroup G`);
3. every neighbourhood of `1` contains a compact open subgroup;
4. the compact open subgroups form a filter basis of `𝓝 1`. -/
@[to_additive /-- **Van Dantzig's theorem (additive).** For a `T₀` (equivalently, Hausdorff)
topological additive group `G`, the following are equivalent:
1. `G` is locally compact and totally disconnected
   (`LocallyCompactSpace G ∧ TotallyDisconnectedSpace G`);
2. `G` is locally compact and nonarchimedean
   (`LocallyCompactSpace G ∧ NonarchimedeanAddGroup G`);
3. every neighbourhood of `0` contains a compact open additive subgroup;
4. the compact open additive subgroups form a filter basis of `𝓝 0`. -/]
theorem vanDantzig_tfae :
    List.TFAE
      [LocallyCompactSpace G ∧ TotallyDisconnectedSpace G,
       LocallyCompactSpace G ∧ NonarchimedeanGroup G,
       ∀ U ∈ 𝓝 (1 : G), ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ U,
       (𝓝 (1 : G)).HasBasis (fun K : OpenSubgroup G ↦ IsCompact (K : Set G))
         fun K ↦ (K : Set G)] := by
  tfae_have 1 → 2 := fun ⟨_, _⟩ ↦ ⟨‹_›, inferInstance⟩
  tfae_have 2 → 4 := fun ⟨_, _⟩ ↦ NonarchimedeanGroup.nhds_one_hasBasis_isCompact_openSubgroup G
  tfae_have 4 → 3 := fun h U hU ↦ h.mem_iff.mp hU
  tfae_have 3 → 1 := fun h ↦ by
    obtain ⟨_, _⟩ := locallyCompactSpace_and_nonarchimedeanGroup_iff.mpr h
    exact ⟨‹_›, inferInstance⟩
  tfae_finish

variable {G}

/-- In a weakly locally compact `T₀` (hence Hausdorff) topological group, total disconnectedness is
equivalent to `NonarchimedeanGroup`. -/
@[to_additive /-- In a weakly locally compact `T₀` (hence Hausdorff) topological additive group,
total disconnectedness is equivalent to `NonarchimedeanAddGroup`. -/]
theorem totallyDisconnectedSpace_iff_nonarchimedeanGroup [WeaklyLocallyCompactSpace G] :
    TotallyDisconnectedSpace G ↔ NonarchimedeanGroup G :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

/-- A `T₀` (hence Hausdorff) topological group is locally compact and totally disconnected if and
only if every neighbourhood of `1` contains a compact open subgroup. -/
@[to_additive /-- A `T₀` (hence Hausdorff) topological additive group is locally compact and
totally disconnected if and only if every neighbourhood of `0` contains a compact open additive
subgroup. -/]
theorem locallyCompactSpace_and_totallyDisconnectedSpace_iff :
    LocallyCompactSpace G ∧ TotallyDisconnectedSpace G ↔
      ∀ U ∈ 𝓝 (1 : G), ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ U :=
  (vanDantzig_tfae G).out 1 3

/-- A `T₀` (hence Hausdorff) topological group is locally compact and totally disconnected if and
only if the compact open subgroups form a basis of `𝓝 1`. -/
@[to_additive /-- A `T₀` (hence Hausdorff) topological additive group is locally compact and
totally disconnected if and only if the compact open additive subgroups form a basis of `𝓝 0`. -/]
theorem locallyCompactSpace_and_totallyDisconnectedSpace_iff_hasBasis :
    LocallyCompactSpace G ∧ TotallyDisconnectedSpace G ↔
      (𝓝 (1 : G)).HasBasis (fun K : OpenSubgroup G ↦ IsCompact (K : Set G))
        fun K ↦ (K : Set G) :=
  (vanDantzig_tfae G).out 1 4

end T0

end IsTopologicalGroup

end
