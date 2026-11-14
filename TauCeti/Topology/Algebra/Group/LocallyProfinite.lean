/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.TFAE
public import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
public import TauCeti.Topology.Algebra.Group.OpenSubgroup.Basic
public import TauCeti.Topology.Algebra.MulAction.Stabilizer
public import TauCeti.Topology.Algebra.Nonarchimedean.Basic
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Separation.Regular
import TauCeti.Topology.Algebra.Group.Pointwise

/-!
# Locally profinite groups and van Dantzig's theorem

A Hausdorff topological group `G` is *locally profinite* (an *l-group*) when it is locally compact
and totally disconnected. In Mathlib's unbundled typeclass hierarchy, `[IsTopologicalGroup G]` and
`[TotallyDisconnectedSpace G]` already synthesize `T2Space G`, and together with
`[WeaklyLocallyCompactSpace G]` they synthesize `ZeroDimensionalSpace G`.

Van Dantzig's theorem identifies locally profinite groups among all Hausdorff topological groups by
three equivalent conditions:
1. `G` is locally compact and totally disconnected
   (`LocallyCompactSpace G ∧ TotallyDisconnectedSpace G`);
2. `G` is locally compact and nonarchimedean (`LocallyCompactSpace G ∧ NonarchimedeanGroup G`);
3. every neighbourhood of `1` contains a compact open subgroup (equivalently, the compact open
   subgroups form a filter basis of `𝓝 (1 : G)`).

For `(1) ⇒ (3)`, intersecting a closed compact identity neighbourhood with the clopen basis of
`ZeroDimensionalSpace G` produces a compact clopen identity neighbourhood `C`, whose
left-translation stabilizer `OpenSubgroup.stabilizer G` is a compact open subgroup inside `C`. This
step requires neither `T2Space G` nor full `LocallyCompactSpace G`: `[WeaklyLocallyCompactSpace G]`
and `[ZeroDimensionalSpace G]` suffice, and register a `NonarchimedeanGroup G` instance extending
`TauCeti.IsTopologicalGroup.nonarchimedeanGroup_of_compactSpace` from compact groups to weakly
locally compact groups. For `(2) ⇒ (3)`, any open subgroup inside a compact identity neighbourhood
is closed and therefore compact. For `(3) ⇒ (1)`, a single compact open subgroup supplies local
compactness via left translation, and the clopen cosets of open subgroups separate points in a
Hausdorff group, making `G` totally separated and hence totally disconnected.

In a locally profinite group, every compact open subgroup `U₀` inherits `IsTopologicalGroup U₀`,
`TotallyDisconnectedSpace U₀`, `T2Space U₀`, `NonarchimedeanGroup U₀`, and (via
`OpenSubgroup.compactSpace_of_isCompact`) `CompactSpace U₀`, so `U₀` is a profinite group in the
unbundled sense; in particular, every identity neighbourhood of `G` contains a compact open
subgroup `V ≤ U₀` whose trace in `U₀` is normal. Moreover, the compact open subgroups contained in
`U₀` form a downward-directed family that is coinitial in `OpenSubgroup G` (cofinal under reverse
inclusion `≥`) and a basis of `𝓝 (1 : G)`.

## Main results

* `OpenSubgroup.isCompact_of_subset_isCompact`, `OpenSubgroup.isCompact_of_le`,
  `OpenSubgroup.compactSpace_iff`, `OpenSubgroup.compactSpace_of_isCompact`: open subgroups inside
  compact sets are compact, and compact open subgroups carry `CompactSpace`.
* `OpenSubgroup.instNonarchimedeanGroup`: open subgroups of nonarchimedean groups are
  nonarchimedean in the subspace topology.
* `OpenSubgroup.isCoinitial_isCompact_and_le`, `OpenSubgroup.directedOn_ge_isCompact_and_le`,
  `OpenSubgroup.directed_ge_isCompact_and_le`, `OpenSubgroup.nhds_one_hasBasis_isCompact_and_le`:
  compact open subgroups contained in a given compact open subgroup `U₀` are downward-directed,
  cofinal under reverse inclusion, and a basis of `𝓝 (1 : G)`.
* `OpenSubgroup.exists_isCompact_le_normal_of_mem_nhds_one`: inside any compact open subgroup `U₀`
  of a totally disconnected topological group, every identity neighbourhood contains a compact open
  subgroup `V ≤ U₀` normal in `U₀`.
* `IsTopologicalGroup.exists_openSubgroup_isCompact_subset`,
  `IsTopologicalGroup.nhds_one_hasBasis_isCompact_openSubgroup`,
  `IsTopologicalGroup.nonarchimedeanGroup_of_weaklyLocallyCompactSpace`: compact open subgroup
  bases and the `NonarchimedeanGroup` instance for weakly locally compact zero-dimensional groups.
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

section Compact

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- An open subgroup contained in a compact set — in particular, in a compact neighbourhood of `1`
— is compact, since open subgroups are closed. -/
@[to_additive /-- An open additive subgroup contained in a compact set — in particular, in a
compact neighbourhood of `0` — is compact, since open additive subgroups are closed. -/]
theorem isCompact_of_subset_isCompact [SeparatelyContinuousMul G] (H : OpenSubgroup G)
    {K : Set G} (hK : IsCompact K) (hHK : (H : Set G) ⊆ K) : IsCompact (H : Set G) :=
  hK.of_isClosed_subset H.isClosed hHK

/-- An open subgroup contained in a compact open subgroup is compact. -/
@[to_additive /-- An open additive subgroup contained in a compact open additive subgroup is
compact. -/]
theorem isCompact_of_le [SeparatelyContinuousMul G] {H U : OpenSubgroup G}
    (hU : IsCompact (U : Set G)) (hHU : H ≤ U) : IsCompact (H : Set G) :=
  H.isCompact_of_subset_isCompact hU hHU

/-- The intersection of a compact open subgroup with any open subgroup is compact. -/
@[to_additive /-- The intersection of a compact open additive subgroup with any open additive
subgroup is compact. -/]
theorem isCompact_inf_of_left [SeparatelyContinuousMul G] {H₁ : OpenSubgroup G}
    (H₂ : OpenSubgroup G) (h₁ : IsCompact (H₁ : Set G)) :
    IsCompact ((H₁ ⊓ H₂ : OpenSubgroup G) : Set G) :=
  isCompact_of_le h₁ inf_le_left

/-- The intersection of any open subgroup with a compact open subgroup is compact. -/
@[to_additive /-- The intersection of any open additive subgroup with a compact open additive
subgroup is compact. -/]
theorem isCompact_inf_of_right [SeparatelyContinuousMul G] (H₁ : OpenSubgroup G)
    {H₂ : OpenSubgroup G} (h₂ : IsCompact (H₂ : Set G)) :
    IsCompact ((H₁ ⊓ H₂ : OpenSubgroup G) : Set G) :=
  isCompact_of_le h₂ inf_le_right

/-- An open subgroup is a compact space in the subspace topology if and only if its underlying set
is compact in the ambient group. -/
@[to_additive /-- An open additive subgroup is a compact space in the subspace topology if and only
if its underlying set is compact in the ambient additive group. -/]
theorem compactSpace_iff (H : OpenSubgroup G) : CompactSpace H ↔ IsCompact (H : Set G) :=
  isCompact_iff_compactSpace.symm

/-- A compact open subgroup is a compact space in the subspace topology. Together with
`OpenSubgroup.instIsTopologicalGroup` and `Subtype.instTotallyDisconnectedSpace`, this equips every
compact open subgroup of a locally profinite group with the unbundled profinite group instances. -/
@[to_additive /-- A compact open additive subgroup is a compact space in the subspace topology.
Together with `OpenAddSubgroup.instIsTopologicalAddGroup` and
`Subtype.instTotallyDisconnectedSpace`, this equips every compact open additive subgroup of a
locally profinite additive group with the unbundled profinite additive group instances. -/]
theorem compactSpace_of_isCompact {H : OpenSubgroup G} (hH : IsCompact (H : Set G)) :
    CompactSpace H :=
  isCompact_iff_compactSpace.mp hH

/-- An open subgroup of a nonarchimedean group is nonarchimedean in the subspace topology. -/
@[to_additive /-- An open additive subgroup of a nonarchimedean additive group is nonarchimedean in
the subspace topology. -/]
instance instNonarchimedeanGroup [NonarchimedeanGroup G] (U : OpenSubgroup G) :
    NonarchimedeanGroup U :=
  inferInstanceAs (NonarchimedeanGroup U.toSubgroup)

/-- The compact open subgroups of `G` are downward-directed (directed under `≥`). -/
@[to_additive /-- The compact open additive subgroups of `G` are downward-directed (directed under
`≥`). -/]
theorem directedOn_ge_isCompact [SeparatelyContinuousMul G] :
    DirectedOn (· ≥ ·) {V : OpenSubgroup G | IsCompact (V : Set G)} :=
  fun V₁ hV₁ V₂ _ ↦ ⟨V₁ ⊓ V₂, isCompact_inf_of_left V₂ hV₁, inf_le_left, inf_le_right⟩

/-- The subtype of compact open subgroups of `G` is directed under reverse inclusion `≥`. -/
@[to_additive /-- The subtype of compact open additive subgroups of `G` is directed under reverse
inclusion `≥`. -/]
theorem directed_ge_isCompact [SeparatelyContinuousMul G] :
    Directed (· ≥ ·) (fun V : {V : OpenSubgroup G // IsCompact (V : Set G)} ↦ V.1) :=
  fun V₁ V₂ ↦ ⟨⟨V₁.1 ⊓ V₂.1, isCompact_inf_of_left V₂.1 V₁.2⟩, inf_le_left, inf_le_right⟩

/-- For any open subgroup `U₀`, the compact open subgroups contained in `U₀` are downward-directed
(directed under `≥`). -/
@[to_additive /-- For any open additive subgroup `U₀`, the compact open additive subgroups
contained in `U₀` are downward-directed (directed under `≥`). -/]
theorem directedOn_ge_isCompact_and_le [SeparatelyContinuousMul G] (U₀ : OpenSubgroup G) :
    DirectedOn (· ≥ ·) {V : OpenSubgroup G | IsCompact (V : Set G) ∧ V ≤ U₀} :=
  fun V₁ hV₁ V₂ _ ↦
    ⟨V₁ ⊓ V₂, ⟨isCompact_inf_of_left V₂ hV₁.1, inf_le_of_left_le hV₁.2⟩, inf_le_left, inf_le_right⟩

/-- For any open subgroup `U₀`, the subtype of compact open subgroups contained in `U₀` is directed
under reverse inclusion `≥`. -/
@[to_additive /-- For any open additive subgroup `U₀`, the subtype of compact open additive
subgroups contained in `U₀` is directed under reverse inclusion `≥`. -/]
theorem directed_ge_isCompact_and_le [SeparatelyContinuousMul G] (U₀ : OpenSubgroup G) :
    Directed (· ≥ ·)
      (fun V : {V : OpenSubgroup G // IsCompact (V : Set G) ∧ V ≤ U₀} ↦ V.1) :=
  fun V₁ V₂ ↦
    ⟨⟨V₁.1 ⊓ V₂.1, isCompact_inf_of_left V₂.1 V₁.2.1, inf_le_of_left_le V₁.2.2⟩,
      inf_le_left, inf_le_right⟩

/-- The family of compact open subgroups contained in a compact open subgroup `U₀` is nonempty. -/
@[to_additive /-- The family of compact open additive subgroups contained in a compact open
additive subgroup `U₀` is nonempty. -/]
theorem nonempty_isCompact_and_le {U₀ : OpenSubgroup G} (hU₀ : IsCompact (U₀ : Set G)) :
    Nonempty {V : OpenSubgroup G // IsCompact (V : Set G) ∧ V ≤ U₀} :=
  ⟨⟨U₀, hU₀, le_rfl⟩⟩

/-- **Cofinality under reverse inclusion.** The compact open subgroups contained in a given compact
open subgroup `U₀` are coinitial in `OpenSubgroup G` (that is, cofinal in `(OpenSubgroup G)ᵒᵈ`
under reverse inclusion `≥`): every open subgroup `W` contains `U₀ ⊓ W`. -/
@[to_additive /-- **Cofinality under reverse inclusion.** The compact open additive subgroups
contained in a given compact open additive subgroup `U₀` are coinitial in `OpenAddSubgroup G` (that
is, cofinal in `(OpenAddSubgroup G)ᵒᵈ` under reverse inclusion `≥`): every open additive subgroup
`W` contains `U₀ ⊓ W`. -/]
theorem isCoinitial_isCompact_and_le [SeparatelyContinuousMul G] {U₀ : OpenSubgroup G}
    (hU₀ : IsCompact (U₀ : Set G)) :
    IsCoinitial {V : OpenSubgroup G | IsCompact (V : Set G) ∧ V ≤ U₀} :=
  fun W ↦ ⟨U₀ ⊓ W, ⟨isCompact_inf_of_left W hU₀, inf_le_left⟩, inf_le_right⟩

/-- In a nonarchimedean group (in particular, in any locally profinite group), the compact open
subgroups contained in a given compact open subgroup `U₀` form a basis of `𝓝 (1 : G)`. -/
@[to_additive /-- In a nonarchimedean additive group (in particular, in any locally profinite
additive group), the compact open additive subgroups contained in a given compact open additive
subgroup `U₀` form a basis of `𝓝 (0 : G)`. -/]
theorem nhds_one_hasBasis_isCompact_and_le [NonarchimedeanGroup G] {U₀ : OpenSubgroup G}
    (hU₀ : IsCompact (U₀ : Set G)) :
    (𝓝 (1 : G)).HasBasis (fun V : OpenSubgroup G ↦ IsCompact (V : Set G) ∧ V ≤ U₀)
      fun V ↦ (V : Set G) where
  mem_iff' s := by
    refine ⟨fun hs ↦ ?_, fun ⟨V, _, hVs⟩ ↦ mem_of_superset V.mem_nhds_one hVs⟩
    obtain ⟨W, hWs⟩ := NonarchimedeanGroup.is_nonarchimedean s hs
    exact ⟨U₀ ⊓ W, ⟨isCompact_inf_of_left W hU₀, inf_le_left⟩, inter_subset_right.trans hWs⟩

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
  have : CompactSpace U₀ := compactSpace_of_isCompact hU₀
  -- Pull `s` back to the profinite group `U₀` and refine an open identity neighbourhood by an open
  -- normal subgroup `N` of `U₀`.
  have hs_sub : (((↑) : U₀ → G) ⁻¹' s) ∈ 𝓝 (1 : U₀) :=
    continuous_subtype_val.continuousAt hs
  obtain ⟨W, hWs, hW_open, h1W⟩ := mem_nhds_iff.mp hs_sub
  let U₀' : Subgroup G := U₀.toSubgroup
  have : CompactSpace U₀' := ‹CompactSpace U₀›
  obtain ⟨N, hNW⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (G := U₀') hW_open h1W
  -- Push `N` forward along the open subtype inclusion `U₀' →* G`.
  let H_sub : Subgroup G := N.toSubgroup.map U₀'.subtype
  have hH_open : IsOpen (H_sub : Set G) := by
    rw [Subgroup.coe_map, Subgroup.coe_subtype]
    exact U₀.isOpen.isOpenMap_subtype_val _ N.toOpenSubgroup.isOpen
  let V : OpenSubgroup G := ⟨H_sub, hH_open⟩
  have hVU₀ : V ≤ U₀ := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hsub : V.toSubgroup.subgroupOf U₀' = N.toSubgroup := by
    ext x
    simp [V, H_sub, Subgroup.mem_subgroupOf]
  refine ⟨V, isCompact_of_le hU₀ hVU₀, hVU₀, ?_, ?_⟩
  · rw [hsub]
    exact N.isNormal'
  · rintro _ ⟨x, hxN, rfl⟩
    exact hWs (hNW hxN)

end Compact

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

/-- In a weakly locally compact nonarchimedean group, the compact open subgroups form a basis of
`𝓝 (1 : G)`. -/
@[to_additive /-- In a weakly locally compact nonarchimedean additive group, the compact open
additive subgroups form a basis of `𝓝 (0 : G)`. -/]
theorem nhds_one_hasBasis_isCompact_openSubgroup (G : Type*) [Group G] [TopologicalSpace G]
    [NonarchimedeanGroup G] [WeaklyLocallyCompactSpace G] :
    (𝓝 (1 : G)).HasBasis (fun H : OpenSubgroup G ↦ IsCompact (H : Set G)) fun H ↦ (H : Set G) :=
  ⟨fun _ ↦
    ⟨exists_openSubgroup_isCompact_subset, fun ⟨H, _, hH⟩ ↦ mem_of_superset H.mem_nhds_one hH⟩⟩

end NonarchimedeanGroup

namespace IsTopologicalGroup

section ZeroDimensional

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [WeaklyLocallyCompactSpace G] [ZeroDimensionalSpace G]

/-- **Van Dantzig's basis step.** In a weakly locally compact zero-dimensional topological group
(in particular, in any locally profinite group), every neighbourhood of `1` contains a compact open
subgroup, constructed as the left-translation stabilizer of a compact clopen identity
neighbourhood. -/
@[to_additive /-- **Van Dantzig's basis step.** In a weakly locally compact zero-dimensional
topological additive group (in particular, in any locally profinite additive group), every
neighbourhood of `0` contains a compact open additive subgroup, constructed as the translation
stabilizer of a compact clopen neighbourhood of `0`. -/]
theorem exists_openSubgroup_isCompact_subset {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ H : OpenSubgroup G, IsCompact (H : Set G) ∧ (H : Set G) ⊆ U := by
  -- Shrink `U` to a closed compact identity neighbourhood `K`, then refine `K` by a clopen `C`.
  obtain ⟨K, hK_mem, -, hK_compact, -, hKU⟩ :=
    TauCeti.exists_mem_nhds_one_isClosed_isCompact_inv_eq_subset hU
  obtain ⟨C, ⟨hC_clopen, h1C⟩, hCK⟩ := (nhds_basis_isClopen (1 : G)).mem_iff.mp hK_mem
  have hC_compact : IsCompact C := hK_compact.of_isClosed_subset hC_clopen.isClosed hCK
  exact ⟨OpenSubgroup.stabilizer G hC_compact hC_clopen.isOpen,
    OpenSubgroup.isCompact_stabilizer hC_compact hC_clopen.isOpen h1C,
    (OpenSubgroup.stabilizer_subset hC_compact hC_clopen.isOpen h1C).trans (hCK.trans hKU)⟩

/-- A weakly locally compact zero-dimensional topological group is nonarchimedean. Since a locally
compact totally disconnected topological group is Hausdorff and therefore zero-dimensional, this
instance applies automatically to every locally profinite group. -/
@[to_additive /-- A weakly locally compact zero-dimensional topological additive group is
nonarchimedean. Since a locally compact totally disconnected topological additive group is
Hausdorff and therefore zero-dimensional, this instance applies automatically to every locally
profinite additive group. -/]
instance (priority := 100) nonarchimedeanGroup_of_weaklyLocallyCompactSpace :
    NonarchimedeanGroup G where
  is_nonarchimedean _ hU :=
    let ⟨H, _, hHU⟩ := exists_openSubgroup_isCompact_subset hU
    ⟨H, hHU⟩

/-- **Compact open subgroups form a basis of `𝓝 1`.** In a weakly locally compact zero-dimensional
topological group (and hence in every locally profinite group), the compact open subgroups form a
filter basis of `𝓝 (1 : G)`. -/
@[to_additive /-- **Compact open additive subgroups form a basis of `𝓝 0`.** In a weakly locally
compact zero-dimensional topological additive group (and hence in every locally profinite additive
group), the compact open additive subgroups form a filter basis of `𝓝 (0 : G)`. -/]
theorem nhds_one_hasBasis_isCompact_openSubgroup (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [WeaklyLocallyCompactSpace G] [ZeroDimensionalSpace G] :
    (𝓝 (1 : G)).HasBasis (fun H : OpenSubgroup G ↦ IsCompact (H : Set G)) fun H ↦ (H : Set G) :=
  NonarchimedeanGroup.nhds_one_hasBasis_isCompact_openSubgroup G

/-- Left cosets of compact open subgroups form a neighbourhood basis at every point `g : G`. -/
@[to_additive /-- Left cosets of compact open additive subgroups form a neighbourhood basis at
every point `g : G`. -/]
theorem nhds_hasBasis_isCompact_openSubgroup (g : G) :
    (𝓝 g).HasBasis (fun H : OpenSubgroup G ↦ IsCompact (H : Set G)) fun H ↦ g • (H : Set G) := by
  have h := (nhds_one_hasBasis_isCompact_openSubgroup G).map (Homeomorph.mulLeft g)
  rw [(Homeomorph.mulLeft g).map_nhds_eq 1] at h
  simpa [← Set.image_smul, smul_eq_mul] using h

/-- In a weakly locally compact zero-dimensional topological group, the compact open subgroups are
coinitial in `OpenSubgroup G` (cofinal under reverse inclusion `≥`). -/
@[to_additive /-- In a weakly locally compact zero-dimensional topological additive group, the
compact open additive subgroups are coinitial in `OpenAddSubgroup G` (cofinal under reverse
inclusion `≥`). -/]
theorem isCoinitial_isCompact_openSubgroup (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [WeaklyLocallyCompactSpace G] [ZeroDimensionalSpace G] :
    IsCoinitial {V : OpenSubgroup G | IsCompact (V : Set G)} := fun W ↦
  exists_openSubgroup_isCompact_subset W.mem_nhds_one

end ZeroDimensional

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
  | ⟨hLC, hTD⟩ => nhds_one_hasBasis_isCompact_openSubgroup G
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
