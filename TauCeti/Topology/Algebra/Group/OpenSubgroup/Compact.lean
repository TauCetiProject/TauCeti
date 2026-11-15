/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.TFAE
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
public import Mathlib.Topology.InductiveDimension.Classes
public import Mathlib.Topology.Separation.Regular
public import TauCeti.Topology.Algebra.Group.OpenSubgroup.Basic
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Topology.InductiveDimension.Functions
import TauCeti.Topology.Algebra.Group.Pointwise
import TauCeti.Topology.Algebra.Nonarchimedean.Profinite

/-!
# Compact open subgroups and van Dantzig's theorem

In a Hausdorff topological group `G`, the following conditions are equivalent (van Dantzig's
theorem):

1. `G` is locally compact and totally disconnected;
2. `G` is locally compact and `NonarchimedeanGroup` (every identity neighbourhood contains an open
   subgroup);
3. every identity neighbourhood contains a compact open subgroup;
4. the compact open subgroups form a basis of the identity filter `𝓝 1`.

A Hausdorff topological group satisfying these equivalent conditions is *locally profinite* (an
`l`-group). Every compact open subgroup of such a group is profinite — a compact, Hausdorff,
totally disconnected, nonarchimedean topological group — and the compact open subgroups contained
in any prescribed open subgroup form a cofinal family directed under reverse inclusion.

The key geometric step from (1) to (3) needs neither `T2Space` nor `TotallyDisconnectedSpace`
once a compact open identity neighbourhood `C` has been chosen: for any compact open set `C` in a
topological group `G`, the left-translation stabilizer `MulAction.stabilizer G C = {g | g • C = C}`
is an open subgroup (`IsCompact.isOpen_stabilizer_of_isOpen`). Indeed, outer regularity of
multiplication against a compact set (`IsCompact.exists_isOpen_superset_mul_subset`) produces an
open identity neighbourhood `V` with `V * C ⊆ C`, and intersecting `V` with `V⁻¹` gives an open
identity neighbourhood stabilizing `C`. When `1 ∈ C`, this stabilizer lies inside `C`; being an
open subgroup it is also closed, hence compact (`IsCompact.isCompact_stabilizer_of_isOpen`). In a
weakly locally compact zero-dimensional topological group, intersecting any identity neighbourhood
with a compact one and extracting a clopen identity neighbourhood therefore yields a basis of
compact open subgroups at `1`
(`TauCeti.IsTopologicalGroup.nhds_one_hasBasis_isCompact_openSubgroup`) without any separation
hypothesis.

Conversely, an open subgroup contained in any compact set is closed and therefore compact
(`OpenSubgroup.isCompact_of_subset`), while a finite open subgroup in a `T₁` group forces the
discrete topology (`OpenSubgroup.discreteTopology_of_finite`).

## Main results

* `IsCompact.isOpen_stabilizer_of_isOpen`, `IsCompact.isCompact_stabilizer_of_isOpen`,
  `IsCompact.exists_isCompact_openSubgroup_subset_of_isOpen`: the left-translation stabilizer of a
  compact open set is an open subgroup, and is compact and contained in `C` when `1 ∈ C` (with
  additive versions).
* `OpenSubgroup.isCompact_of_subset`, `OpenSubgroup.isCompact_inf_left`,
  `OpenSubgroup.isCompact_inf_right`: compactness of open subgroups contained in compact sets and
  stability under intersection with arbitrary open subgroups.
* `OpenSubgroup.directedOn_isCompact_le`, `OpenSubgroup.nhds_one_hasBasis_isCompact_le`: compact
  open subgroups inside a given open subgroup are directed under `≥` and form a basis of `𝓝 1`.
* `OpenSubgroup.discreteTopology_of_finite`: a finite open subgroup in a `T₁` group implies the
  discrete topology.
* `OpenSubgroup.nonarchimedeanGroup_of_isCompact`: every compact open subgroup of a
  zero-dimensional topological group is nonarchimedean (hence profinite when Hausdorff).
* `NonarchimedeanGroup.nhds_one_hasBasis_isCompact_openSubgroup`,
  `TauCeti.IsTopologicalGroup.nhds_one_hasBasis_isCompact_openSubgroup`: compact open subgroups
  form a neighbourhood basis of `1`.
* `TauCeti.IsTopologicalGroup.totallyDisconnectedSpace_iff_nonarchimedeanGroup`,
  `TauCeti.IsTopologicalGroup.locallyCompactSpace_and_totallyDisconnectedSpace_iff`,
  `TauCeti.IsTopologicalGroup.locallyProfinite_tfae`: van Dantzig's equivalence for Hausdorff
  topological groups, together with additive counterparts.

## References

* J. N. Bernstein, *Representations of `p`-adic Groups*, Harvard University lecture notes written
  by K. E. Rumelhart (1992), Ch. I §1.1, Definition 1, p. 7.
* L. Kramer, *Locally Compact Groups: Some Lectures on Topological Groups and Building Theory*,
  Universität Münster lecture notes, Lemma 1.41, Proposition 1.43, and Theorem 1.44, pp. 17–19.
-/

public section

open Filter Set Topology
open scoped Pointwise

section TranslationStabilizer

variable {G : Type*} [Group G]

/-- The left-translation stabilizer of a subgroup `H` viewed as a subset of `G` is `H` itself. -/
@[to_additive (attr := simp) /-- The translation stabilizer of an additive subgroup `H` viewed as
a subset of `G` is `H` itself. -/]
theorem Subgroup.stabilizer_coe (H : Subgroup G) :
    MulAction.stabilizer G (H : Set G) = H := by
  ext g
  refine ⟨fun hg ↦ ?_, fun hg ↦ smul_coe_set hg⟩
  have hmem : g • (1 : G) ∈ g • (H : Set G) := smul_mem_smul_set H.one_mem
  rw [MulAction.mem_stabilizer_iff.mp hg, smul_eq_mul, mul_one] at hmem
  exact hmem

/-- Elements stabilizing a subset `C` under left translation belong to `C` whenever `1 ∈ C`. -/
@[to_additive /-- Elements stabilizing a subset `C` under translation belong to `C` whenever
`0 ∈ C`. -/]
theorem TauCeti.stabilizer_set_subset_of_one_mem {C : Set G} (h1 : (1 : G) ∈ C) :
    (MulAction.stabilizer G C : Set G) ⊆ C := by
  intro g hg
  have hmem : g • (1 : G) ∈ g • C := smul_mem_smul_set h1
  rwa [MulAction.mem_stabilizer_iff.mp hg, smul_eq_mul, mul_one] at hmem

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- The left-translation stabilizer `{g : G | g • C = C}` of a compact open subset `C` of a
topological group is an open subgroup. -/
@[to_additive IsCompact.isOpen_addStabilizer_of_isOpen
/-- The translation stabilizer `{g : G | g +ᵥ C = C}` of a compact open subset `C` of a topological
additive group is an open additive subgroup. -/]
theorem IsCompact.isOpen_stabilizer_of_isOpen {C : Set G} (hC : IsCompact C) (hCo : IsOpen C) :
    IsOpen (MulAction.stabilizer G C : Set G) := by
  have h1C : ({(1 : G)} : Set G) * C ⊆ C := by simp
  obtain ⟨V, hVo, h1V, hVC⟩ := hC.exists_isOpen_superset_mul_subset hCo h1C
  have hV1 : (1 : G) ∈ V := h1V rfl
  have hW_nhds : V ∩ V⁻¹ ∈ 𝓝 (1 : G) :=
    (hVo.inter hVo.inv).mem_nhds ⟨hV1, by simpa using hV1⟩
  refine (MulAction.stabilizer G C).isOpen_of_mem_nhds (mem_of_superset hW_nhds ?_)
  rintro g ⟨hgV, hginvV⟩
  have hsub : ∀ {x : G}, x ∈ V → x • C ⊆ C := by
    rintro x hx _ ⟨c, hc, rfl⟩
    exact hVC (mul_mem_mul hx hc)
  refine SetLike.mem_coe.mpr (MulAction.mem_stabilizer_iff.mpr (Subset.antisymm (hsub hgV) ?_))
  intro c hc
  have hinv : g⁻¹ • c ∈ C := hsub hginvV (smul_mem_smul_set hc)
  simpa using smul_mem_smul_set (a := g) hinv

/-- The left-translation stabilizer of a compact open identity neighbourhood is compact. -/
@[to_additive IsCompact.isCompact_addStabilizer_of_isOpen
/-- The translation stabilizer of a compact open neighbourhood of zero is compact. -/]
theorem IsCompact.isCompact_stabilizer_of_isOpen {C : Set G} (hC : IsCompact C) (hCo : IsOpen C)
    (h1 : (1 : G) ∈ C) : IsCompact (MulAction.stabilizer G C : Set G) :=
  hC.of_isClosed_subset
    ((MulAction.stabilizer G C).isClosed_of_isOpen (hC.isOpen_stabilizer_of_isOpen hCo))
    (TauCeti.stabilizer_set_subset_of_one_mem h1)

/-- Every compact open identity neighbourhood in a topological group contains a compact open
subgroup, namely its left-translation stabilizer. -/
@[to_additive /-- Every compact open neighbourhood of zero in a topological additive group
contains a compact open additive subgroup, namely its translation stabilizer. -/]
theorem IsCompact.exists_isCompact_openSubgroup_subset_of_isOpen {C : Set G} (hC : IsCompact C)
    (hCo : IsOpen C) (h1 : (1 : G) ∈ C) :
    ∃ H : OpenSubgroup G, IsCompact (H : Set G) ∧ (H : Set G) ⊆ C :=
  ⟨⟨MulAction.stabilizer G C, hC.isOpen_stabilizer_of_isOpen hCo⟩,
    hC.isCompact_stabilizer_of_isOpen hCo h1,
    TauCeti.stabilizer_set_subset_of_one_mem h1⟩

end TranslationStabilizer

namespace OpenSubgroup

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- An open subgroup of a zero-dimensional group is zero-dimensional. -/
@[to_additive /-- An open additive subgroup of a zero-dimensional additive group is
zero-dimensional. -/]
instance instZeroDimensionalSpace [ZeroDimensionalSpace G] (U : OpenSubgroup G) :
    ZeroDimensionalSpace U :=
  Topology.IsInducing.subtypeVal.hasSmallInductiveDimensionLT ‹_›

section SeparatelyContinuousMul

variable [SeparatelyContinuousMul G]

/-- Any open subgroup contained in a compact subset is compact, because an open subgroup is
closed. -/
@[to_additive /-- Any open additive subgroup contained in a compact subset is compact, because an
open additive subgroup is closed. -/]
theorem isCompact_of_subset (U : OpenSubgroup G) {K : Set G} (hK : IsCompact K)
    (hUK : (U : Set G) ⊆ K) : IsCompact (U : Set G) :=
  hK.of_isClosed_subset U.isClosed hUK

/-- The intersection of a compact open subgroup with any open subgroup is compact. -/
@[to_additive /-- The intersection of a compact open additive subgroup with any open additive
subgroup is compact. -/]
theorem isCompact_inf_left {U : OpenSubgroup G} (hU : IsCompact (U : Set G))
    (V : OpenSubgroup G) : IsCompact ((U ⊓ V : OpenSubgroup G) : Set G) :=
  (U ⊓ V).isCompact_of_subset hU inter_subset_left

/-- The intersection of any open subgroup with a compact open subgroup is compact. -/
@[to_additive /-- The intersection of any open additive subgroup with a compact open additive
subgroup is compact. -/]
theorem isCompact_inf_right (U : OpenSubgroup G) {V : OpenSubgroup G}
    (hV : IsCompact (V : Set G)) : IsCompact ((U ⊓ V : OpenSubgroup G) : Set G) :=
  (U ⊓ V).isCompact_of_subset hV inter_subset_right

/-- Compact open subgroups contained in a given open subgroup `U` form a family directed under
reverse inclusion `≥`. -/
@[to_additive /-- Compact open additive subgroups contained in a given open additive subgroup `U`
form a family directed under reverse inclusion `≥`. -/]
theorem directedOn_isCompact_le (U : OpenSubgroup G) :
    DirectedOn (· ≥ ·) {V : OpenSubgroup G | IsCompact (V : Set G) ∧ V ≤ U} := by
  rintro V₁ ⟨hV₁c, hV₁U⟩ V₂ ⟨_, _⟩
  exact ⟨V₁ ⊓ V₂, ⟨isCompact_inf_left hV₁c V₂, inf_le_of_left_le hV₁U⟩, inf_le_left, inf_le_right⟩

/-- If a `T₁` group with separately continuous multiplication has a finite open subgroup, its
topology is discrete. -/
@[to_additive /-- If a `T₁` additive group with separately continuous addition has a finite open
additive subgroup, its topology is discrete. -/]
theorem discreteTopology_of_finite [T1Space G] (U : OpenSubgroup G) (hU : (U : Set G).Finite) :
    DiscreteTopology G := by
  rw [discreteTopology_iff_isOpen_singleton_one]
  have heq : ({(1 : G)} : Set G) = (U : Set G) \ ((U : Set G) \ {(1 : G)}) := by
    ext x
    simp only [mem_singleton_iff, Set.mem_sdiff, SetLike.mem_coe]
    exact ⟨fun hx ↦ ⟨hx ▸ U.one_mem, fun h ↦ h.2 hx⟩, fun hx ↦ by tauto⟩
  rw [heq]
  exact U.isOpen.sdiff (hU.sdiff.isClosed)

end SeparatelyContinuousMul

/-- Every compact open subgroup of a zero-dimensional topological group is nonarchimedean. When the
ambient group is Hausdorff, `U` is therefore profinite: compact, Hausdorff, totally disconnected,
and nonarchimedean. -/
@[to_additive /-- Every compact open additive subgroup of a zero-dimensional topological additive
group is nonarchimedean. -/]
theorem nonarchimedeanGroup_of_isCompact [IsTopologicalGroup G] [ZeroDimensionalSpace G]
    {U : OpenSubgroup G} (hU : IsCompact (U : Set G)) : NonarchimedeanGroup U := by
  have : CompactSpace U := isCompact_iff_compactSpace.mp hU
  exact TauCeti.IsTopologicalGroup.nonarchimedeanGroup_of_compactSpace

end OpenSubgroup

namespace NonarchimedeanGroup

/-- In a weakly locally compact nonarchimedean topological group, the compact open subgroups form a
basis of `𝓝 1`. -/
@[to_additive /-- In a weakly locally compact nonarchimedean topological additive group, the
compact open additive subgroups form a basis of `𝓝 0`. -/]
theorem nhds_one_hasBasis_isCompact_openSubgroup (G : Type*) [Group G] [TopologicalSpace G]
    [NonarchimedeanGroup G] [WeaklyLocallyCompactSpace G] :
    (𝓝 (1 : G)).HasBasis (fun H : OpenSubgroup G ↦ IsCompact (H : Set G))
      fun H ↦ (H : Set G) := by
  refine ⟨fun W ↦ ⟨fun hW ↦ ?_, fun ⟨H, _, hHW⟩ ↦ mem_of_superset H.mem_nhds_one hHW⟩⟩
  obtain ⟨K, hKc, hK⟩ := exists_compact_mem_nhds (1 : G)
  obtain ⟨H, hH⟩ := NonarchimedeanGroup.is_nonarchimedean (W ∩ K) (inter_mem hW hK)
  exact ⟨H, H.isCompact_of_subset hKc (hH.trans inter_subset_right), hH.trans inter_subset_left⟩

end NonarchimedeanGroup

namespace TauCeti

namespace IsTopologicalGroup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Every identity neighbourhood in a weakly locally compact zero-dimensional topological group
contains a compact open subgroup. In particular, this applies to every locally compact Hausdorff
totally disconnected group (`van Dantzig's theorem`). -/
@[to_additive IsTopologicalAddGroup.exists_isCompact_openAddSubgroup_subset
/-- Every neighbourhood of zero in a weakly locally compact zero-dimensional topological additive
group contains a compact open additive subgroup. -/]
theorem exists_isCompact_openSubgroup_subset [WeaklyLocallyCompactSpace G] [ZeroDimensionalSpace G]
    {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ H : OpenSubgroup G, IsCompact (H : Set G) ∧ (H : Set G) ⊆ U := by
  obtain ⟨K, hKc, hK⟩ := exists_compact_mem_nhds (1 : G)
  obtain ⟨C, ⟨hCcl, h1C⟩, hCUK⟩ := (nhds_basis_isClopen (1 : G)).mem_iff.mp (inter_mem hU hK)
  have hCc : IsCompact C := hKc.of_isClosed_subset hCcl.isClosed (hCUK.trans inter_subset_right)
  obtain ⟨H, hHc, hHC⟩ := hCc.exists_isCompact_openSubgroup_subset_of_isOpen hCcl.isOpen h1C
  exact ⟨H, hHc, hHC.trans (hCUK.trans inter_subset_left)⟩

/-- In a weakly locally compact zero-dimensional topological group, the compact open subgroups form
a basis of `𝓝 1`. -/
@[to_additive IsTopologicalAddGroup.nhds_zero_hasBasis_isCompact_openAddSubgroup
/-- In a weakly locally compact zero-dimensional topological additive group, the compact open
additive subgroups form a basis of `𝓝 0`. -/]
theorem nhds_one_hasBasis_isCompact_openSubgroup (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [WeaklyLocallyCompactSpace G] [ZeroDimensionalSpace G] :
    (𝓝 (1 : G)).HasBasis (fun H : OpenSubgroup G ↦ IsCompact (H : Set G))
      fun H ↦ (H : Set G) :=
  ⟨fun _ ↦ ⟨exists_isCompact_openSubgroup_subset,
    fun ⟨H, _, hH⟩ ↦ mem_of_superset H.mem_nhds_one hH⟩⟩

/-- A weakly locally compact zero-dimensional topological group is nonarchimedean. -/
@[to_additive IsTopologicalAddGroup.nonarchimedeanAddGroup_of_weaklyLocallyCompactSpace
/-- A weakly locally compact zero-dimensional topological additive group is nonarchimedean. -/]
theorem nonarchimedeanGroup_of_weaklyLocallyCompactSpace [WeaklyLocallyCompactSpace G]
    [ZeroDimensionalSpace G] : NonarchimedeanGroup G where
  is_nonarchimedean _ hU :=
    let ⟨H, _, hHU⟩ := exists_isCompact_openSubgroup_subset hU
    ⟨H, hHU⟩

/-- In a weakly locally compact Hausdorff topological group, total disconnectedness is equivalent
to the `NonarchimedeanGroup` property. -/
@[to_additive IsTopologicalAddGroup.totallyDisconnectedSpace_iff_nonarchimedeanAddGroup
/-- In a weakly locally compact Hausdorff topological additive group, total disconnectedness is
equivalent to the `NonarchimedeanAddGroup` property. -/]
theorem totallyDisconnectedSpace_iff_nonarchimedeanGroup [T2Space G]
    [WeaklyLocallyCompactSpace G] :
    TotallyDisconnectedSpace G ↔ NonarchimedeanGroup G :=
  ⟨fun _ ↦ nonarchimedeanGroup_of_weaklyLocallyCompactSpace,
    fun _ ↦
      have : TotallySeparatedSpace G := NonarchimedeanGroup.instTotallySeparated
      inferInstance⟩

/-- **Van Dantzig's theorem** (locally compact and totally disconnected form): a Hausdorff
topological group is locally compact and totally disconnected if and only if every identity
neighbourhood contains a compact open subgroup. -/
@[to_additive IsTopologicalAddGroup.locallyCompactSpace_and_totallyDisconnectedSpace_iff
/-- **Van Dantzig's theorem** (additive form): a Hausdorff topological additive group is locally
compact and totally disconnected if and only if every neighbourhood of zero contains a compact open
additive subgroup. -/]
theorem locallyCompactSpace_and_totallyDisconnectedSpace_iff [T2Space G] :
    LocallyCompactSpace G ∧ TotallyDisconnectedSpace G ↔
      ∀ U ∈ 𝓝 (1 : G), ∃ H : OpenSubgroup G, IsCompact (H : Set G) ∧ (H : Set G) ⊆ U := by
  constructor
  · rintro ⟨_, _⟩ _ hU
    exact exists_isCompact_openSubgroup_subset hU
  · intro h
    obtain ⟨H₀, hH₀c, _⟩ := h univ univ_mem
    have hLC : LocallyCompactSpace G :=
      hH₀c.locallyCompactSpace_of_mem_nhds_of_group H₀.mem_nhds_one
    have hNA : NonarchimedeanGroup G :=
      ⟨fun U hU ↦ let ⟨H, _, hHU⟩ := h U hU; ⟨H, hHU⟩⟩
    exact ⟨hLC, totallyDisconnectedSpace_iff_nonarchimedeanGroup.mpr hNA⟩

/-- A Hausdorff topological group is locally compact and nonarchimedean if and only if every
identity neighbourhood contains a compact open subgroup. -/
@[to_additive IsTopologicalAddGroup.locallyCompactSpace_and_nonarchimedeanAddGroup_iff
/-- A Hausdorff topological additive group is locally compact and nonarchimedean if and only if
every neighbourhood of zero contains a compact open additive subgroup. -/]
theorem locallyCompactSpace_and_nonarchimedeanGroup_iff [T2Space G] :
    LocallyCompactSpace G ∧ NonarchimedeanGroup G ↔
      ∀ U ∈ 𝓝 (1 : G), ∃ H : OpenSubgroup G, IsCompact (H : Set G) ∧ (H : Set G) ⊆ U := by
  refine ⟨fun ⟨_, _⟩ _ hU ↦
    (NonarchimedeanGroup.nhds_one_hasBasis_isCompact_openSubgroup G).mem_iff.mp hU, fun h ↦ ?_⟩
  obtain ⟨hLC, _⟩ := locallyCompactSpace_and_totallyDisconnectedSpace_iff.mpr h
  exact ⟨hLC, ⟨fun U hU ↦ let ⟨H, _, hHU⟩ := h U hU; ⟨H, hHU⟩⟩⟩

/-- **Van Dantzig's theorem**: in a Hausdorff topological group, local compactness plus total
disconnectedness, local compactness plus `NonarchimedeanGroup`, existence of compact open subgroups
inside every identity neighbourhood, and the filter-basis property of compact open subgroups at `1`
are all equivalent. -/
@[to_additive IsTopologicalAddGroup.locallyProfinite_tfae
/-- **Van Dantzig's theorem** (additive form): in a Hausdorff topological additive group, local
compactness plus total disconnectedness, local compactness plus `NonarchimedeanAddGroup`, existence
of compact open additive subgroups inside every zero neighbourhood, and the filter-basis property
of compact open additive subgroups at `0` are all equivalent. -/]
theorem locallyProfinite_tfae (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] :
    List.TFAE
      [ LocallyCompactSpace G ∧ TotallyDisconnectedSpace G,
        LocallyCompactSpace G ∧ NonarchimedeanGroup G,
        ∀ U ∈ 𝓝 (1 : G), ∃ H : OpenSubgroup G, IsCompact (H : Set G) ∧ (H : Set G) ⊆ U,
        (𝓝 (1 : G)).HasBasis (fun H : OpenSubgroup G ↦ IsCompact (H : Set G))
          fun H ↦ (H : Set G) ] := by
  tfae_have 1 ↔ 3 := locallyCompactSpace_and_totallyDisconnectedSpace_iff
  tfae_have 2 ↔ 3 := locallyCompactSpace_and_nonarchimedeanGroup_iff
  tfae_have 3 ↔ 4 := ⟨fun h ↦ ⟨fun _ ↦ ⟨h _, fun ⟨H, _, hH⟩ ↦ mem_of_superset H.mem_nhds_one hH⟩⟩,
    fun h _ hU ↦ h.mem_iff.mp hU⟩
  tfae_finish

end IsTopologicalGroup

end TauCeti

namespace OpenSubgroup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [WeaklyLocallyCompactSpace G] [ZeroDimensionalSpace G]

/-- For any open subgroup `U` of a weakly locally compact zero-dimensional topological group, the
compact open subgroups contained in `U` form a basis of `𝓝 1` (and hence are cofinal in all open
subgroups under reverse inclusion). -/
@[to_additive /-- For any open additive subgroup `U` of a weakly locally compact zero-dimensional
topological additive group, the compact open additive subgroups contained in `U` form a basis of
`𝓝 0`. -/]
theorem nhds_one_hasBasis_isCompact_le (U : OpenSubgroup G) :
    (𝓝 (1 : G)).HasBasis (fun V : OpenSubgroup G ↦ IsCompact (V : Set G) ∧ V ≤ U)
      fun V ↦ (V : Set G) := by
  refine ⟨fun W ↦ ⟨fun hW ↦ ?_, fun ⟨V, _, hVW⟩ ↦ mem_of_superset V.mem_nhds_one hVW⟩⟩
  obtain ⟨H, hHc, hH⟩ :=
    TauCeti.IsTopologicalGroup.exists_isCompact_openSubgroup_subset (inter_mem hW U.mem_nhds_one)
  exact ⟨H, ⟨hHc, hH.trans inter_subset_right⟩, hH.trans inter_subset_left⟩

/-- Every open subgroup of a weakly locally compact zero-dimensional topological group contains a
compact open subgroup. -/
@[to_additive /-- Every open additive subgroup of a weakly locally compact zero-dimensional
topological additive group contains a compact open additive subgroup. -/]
theorem exists_isCompact_le (U : OpenSubgroup G) :
    ∃ V : OpenSubgroup G, IsCompact (V : Set G) ∧ V ≤ U := by
  obtain ⟨V, hV, -⟩ := (U.nhds_one_hasBasis_isCompact_le.mem_iff).mp univ_mem
  exact ⟨V, hV⟩

end OpenSubgroup
