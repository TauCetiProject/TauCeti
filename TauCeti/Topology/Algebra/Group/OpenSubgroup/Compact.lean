/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Pointwise.Stabilizer
public import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
public import Mathlib.Topology.Separation.Regular
public import TauCeti.Topology.Algebra.Group.OpenSubgroup.Basic
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Separation.Connected
import TauCeti.Topology.Algebra.Nonarchimedean.OpenSubgroupBasis

/-!
# Compact open subgroups and van Dantzig's theorem

A Hausdorff topological group is *locally profinite* (an *l-group*) when its compact open
subgroups form a basis of neighbourhoods of the identity. Van Dantzig's theorem says that this
happens exactly when the group is locally compact and totally disconnected, and also exactly when
it is locally compact and nonarchimedean. Locally profinite groups are the groups whose smooth
representations are studied in the representation theory of `p`-adic groups: there a vector is
smooth when it is fixed by a compact open subgroup, so the basis of compact open subgroups is what
makes smoothness and invariants under compact open subgroups interchangeable.

The argument is the translation stabilizer of a compact open set `C`. Compactness of `C` and
continuity of multiplication give an identity neighbourhood `V` with `V * C ⊆ C`, so `C` is
stabilised by `V ∩ V⁻¹` and its stabilizer `{g | g • C = C}` is an open subgroup. When `1 ∈ C`
the stabilizer lies inside `C`, hence is compact, being closed. In a zero-dimensional, weakly
locally compact group, such as a Hausdorff, totally disconnected, weakly locally compact group,
the compact clopen sets form a basis at the identity, so every identity neighbourhood contains a
compact open subgroup.

## Main results

* `IsCompact.isOpen_stabilizer`: the left translation stabilizer of a compact open set is open.
* `IsCompact.exists_openSubgroup_subset`: a compact open set containing the identity contains a
  compact open subgroup.
* `TauCeti.IsTopologicalGroup.nonarchimedeanGroup_of_weaklyLocallyCompactSpace`: a
  zero-dimensional, weakly locally compact topological group is nonarchimedean. This covers
  Hausdorff, totally disconnected, locally compact groups, and in particular profinite groups.
* `NonarchimedeanGroup.nhds_one_hasBasis_isCompact_openSubgroup`: in a weakly locally compact
  nonarchimedean group the compact open subgroups form a basis of neighbourhoods of the identity.
* `NonarchimedeanGroup.nhds_hasBasis_isCompact_openSubgroup`,
  `NonarchimedeanGroup.isCoinitial_isCompact_openSubgroup`: left cosets of compact open subgroups
  form a basis at every point, and the compact open subgroups are coinitial among open subgroups.
* `NonarchimedeanGroup.eq_one_of_forall_mem_isCompact_openSubgroup`,
  `NonarchimedeanGroup.discreteTopology_of_forall_isCompact_openSubgroup_le`: in a T1 such group
  the compact open subgroups meet in `{1}`, so an open subgroup inside all of them makes the
  group discrete.
* `Subgroup.isOpen_iff_exists_isCompact_openSubgroup_le`: in such a group a subgroup is open
  exactly when it contains a compact open subgroup.
* `OpenSubgroup.directedOn_isCompact`: the compact open subgroups are directed under reverse
  inclusion.
* `OpenSubgroup.nhds_one_hasBasis_isCompact_and_le`,
  `OpenSubgroup.exists_isCompact_le_normal_of_mem_nhds_one`: the compact open subgroups inside a
  compact open subgroup `U₀` form a basis at the identity, and can be chosen normal in `U₀`.
* `TauCeti.IsTopologicalGroup.locallyCompact_totallyDisconnected_tfae`: van Dantzig's theorem,
  the equivalence of the three descriptions of a locally profinite group.

All results have additive versions.

## References

* J. Bernstein, *Representations of p-adic groups*, Harvard lectures 1992, written by
  K. Rumelhart, Chapter I, §1.1, p. 7.
* L. Kramer, *Locally Compact Groups and Lie Groups*, Chapter 1, version of 19 May 2020,
  Lemma 1.41, Proposition 1.43 and Theorem 1.44, pp. 17–19. Lemma 1.41 is the translation
  stabilizer argument, with right translations where this file uses left translations.
-/

public section

open Set Filter
open scoped Pointwise Topology

variable {G : Type*} [Group G] [TopologicalSpace G]

section Stabilizer

variable [IsTopologicalGroup G] {C : Set G}

/-- In a topological group, the left translation stabilizer `{g | g • C = C}` of a compact open
set `C` is open. -/
@[to_additive IsCompact.isOpen_addStabilizer /-- In a topological additive group, the translation
stabilizer `{g | g +ᵥ C = C}` of a compact open set `C` is open. -/]
theorem IsCompact.isOpen_stabilizer (hC : IsCompact C) (hCo : IsOpen C) :
    IsOpen (MulAction.stabilizer G C : Set G) := by
  obtain ⟨V, hV, hVC⟩ := compact_open_separated_mul_left hC hCo subset_rfl
  have hsub (g : G) (hg : g ∈ V) : g • C ⊆ C := (smul_set_subset_mul hg).trans hVC
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  filter_upwards [hV, inv_mem_nhds_one G hV] with g hg hg'
  refine MulAction.mem_stabilizer_iff.2 ((hsub g hg).antisymm fun c hc ↦ ?_)
  exact ⟨g⁻¹ • c, hsub g⁻¹ hg' (smul_mem_smul_set hc), smul_inv_smul g c⟩

/-- **Compact open subgroups inside compact open sets.** In a topological group, a compact open
set containing the identity contains a compact open subgroup: its left translation stabilizer. -/
@[to_additive /-- In a topological additive group, a compact open set containing zero contains a
compact open additive subgroup: its translation stabilizer. -/]
theorem IsCompact.exists_openSubgroup_subset (hC : IsCompact C) (hCo : IsOpen C)
    (h1 : (1 : G) ∈ C) : ∃ H : OpenSubgroup G, IsCompact (H : Set G) ∧ (H : Set G) ⊆ C := by
  let H : OpenSubgroup G := ⟨MulAction.stabilizer G C, hC.isOpen_stabilizer hCo⟩
  have hHC : (H : Set G) ⊆ C := fun h hh ↦ by
    simpa [MulAction.mem_stabilizer_iff.1 hh] using smul_mem_smul_set (a := h) h1
  exact ⟨H, hC.of_isClosed_subset H.isClosed hHC, hHC⟩

end Stabilizer

/-- The compact open subgroups of a topological group are directed under reverse inclusion: the
intersection of two of them is again one. -/
@[to_additive /-- The compact open additive subgroups of a topological additive group are
directed under reverse inclusion. -/]
theorem OpenSubgroup.directedOn_isCompact [SeparatelyContinuousMul G] :
    DirectedOn (· ≥ ·) {H : OpenSubgroup G | IsCompact (H : Set G)} := fun H₁ h₁ H₂ _ ↦
  ⟨H₁ ⊓ H₂, h₁.of_isClosed_subset (H₁ ⊓ H₂).isClosed inter_subset_left, inf_le_left, inf_le_right⟩

/-- In a weakly locally compact nonarchimedean group the compact open subgroups form a basis of
neighbourhoods of the identity. -/
@[to_additive /-- In a weakly locally compact nonarchimedean additive group the compact open
additive subgroups form a basis of neighbourhoods of zero. -/]
theorem NonarchimedeanGroup.nhds_one_hasBasis_isCompact_openSubgroup [NonarchimedeanGroup G]
    [WeaklyLocallyCompactSpace G] :
    (𝓝 (1 : G)).HasBasis (fun H : OpenSubgroup G ↦ IsCompact (H : Set G)) (↑) := by
  refine ⟨fun U ↦ ⟨fun hU ↦ ?_, fun ⟨H, _, hHU⟩ ↦ mem_of_superset H.mem_nhds_one hHU⟩⟩
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G)
  obtain ⟨H, hH⟩ := NonarchimedeanGroup.is_nonarchimedean _ (inter_mem hU hK1)
  exact ⟨H, hK.of_isClosed_subset H.isClosed (hH.trans inter_subset_right),
    hH.trans inter_subset_left⟩

namespace NonarchimedeanGroup

variable [NonarchimedeanGroup G] [WeaklyLocallyCompactSpace G]

/-- In a weakly locally compact nonarchimedean group, left cosets of compact open subgroups form a
neighbourhood basis at every point `g : G`. -/
@[to_additive /-- In a weakly locally compact nonarchimedean additive group, left cosets of compact
open additive subgroups form a neighbourhood basis at every point `g : G`. -/]
theorem nhds_hasBasis_isCompact_openSubgroup (g : G) :
    (𝓝 g).HasBasis (fun H : OpenSubgroup G ↦ IsCompact (H : Set G)) fun H ↦ g • (H : Set G) := by
  have h := (nhds_one_hasBasis_isCompact_openSubgroup (G := G)).map (Homeomorph.mulLeft g)
  rw [(Homeomorph.mulLeft g).map_nhds_eq 1] at h
  simpa [← Set.image_smul, smul_eq_mul] using h

/-- In a weakly locally compact nonarchimedean group, the compact open subgroups are coinitial in
`OpenSubgroup G` (cofinal under reverse inclusion `≥`). -/
@[to_additive /-- In a weakly locally compact nonarchimedean additive group, the compact open
additive subgroups are coinitial in `OpenAddSubgroup G` (cofinal under reverse inclusion `≥`). -/]
theorem isCoinitial_isCompact_openSubgroup :
    IsCoinitial {V : OpenSubgroup G | IsCompact (V : Set G)} := fun W ↦
  (nhds_one_hasBasis_isCompact_openSubgroup (G := G)).mem_iff.1 W.mem_nhds_one

variable [T1Space G]

/-- In a T1, weakly locally compact nonarchimedean group, an element lying in every compact open
subgroup is the identity: some compact open subgroup lies in the neighbourhood `{g}ᶜ` of `1`. -/
@[to_additive /-- In a T1, weakly locally compact nonarchimedean additive group, an element lying
in every compact open additive subgroup is zero. -/]
theorem eq_one_of_forall_mem_isCompact_openSubgroup {g : G}
    (h : ∀ V : OpenSubgroup G, IsCompact (V : Set G) → g ∈ V) : g = 1 := by
  by_contra hne
  obtain ⟨V, hVc, hVg⟩ := (nhds_one_hasBasis_isCompact_openSubgroup (G := G)).mem_iff.1
    (isOpen_compl_singleton.mem_nhds (Ne.symm hne))
  exact hVg (h V hVc) rfl

/-- A T1, weakly locally compact nonarchimedean group is discrete as soon as some open subgroup `U`
lies in every compact open subgroup: then `U = {1}`. -/
@[to_additive /-- A T1, weakly locally compact nonarchimedean additive group is discrete as soon
as some open additive subgroup `U` lies in every compact open additive subgroup. -/]
theorem discreteTopology_of_forall_isCompact_openSubgroup_le {U : OpenSubgroup G}
    (h : ∀ V : OpenSubgroup G, IsCompact (V : Set G) → U ≤ V) : DiscreteTopology G := by
  refine discreteTopology_of_isOpen_singleton_one ?_
  convert U.isOpen using 1
  exact Set.ext fun g ↦ ⟨fun hg ↦ hg ▸ U.one_mem,
    fun hg ↦ eq_one_of_forall_mem_isCompact_openSubgroup fun V hV ↦ h V hV hg⟩

end NonarchimedeanGroup

/-- In a weakly locally compact nonarchimedean group, a subgroup is open exactly when it contains
a compact open subgroup. -/
@[to_additive /-- In a weakly locally compact nonarchimedean additive group, an additive subgroup
is open exactly when it contains a compact open additive subgroup. -/]
theorem Subgroup.isOpen_iff_exists_isCompact_openSubgroup_le [NonarchimedeanGroup G]
    [WeaklyLocallyCompactSpace G] (H : Subgroup G) :
    IsOpen (H : Set G) ↔ ∃ U : OpenSubgroup G, IsCompact (U : Set G) ∧ (U : Subgroup G) ≤ H :=
  ⟨fun hH ↦ NonarchimedeanGroup.nhds_one_hasBasis_isCompact_openSubgroup.mem_iff.1
    (hH.mem_nhds H.one_mem), fun ⟨_, _, hUH⟩ ↦ H.isOpen_of_openSubgroup hUH⟩

namespace OpenSubgroup

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
    (fun W _ ↦ isCoinitial_isCompact_and_le hU₀ W) fun V _ ↦ V.mem_nhds_one

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
    continuous_subtypeVal.continuousAt hs
  obtain ⟨W, hWs, hW_open, h1W⟩ := mem_nhds_iff.mp hs_sub
  obtain ⟨N, hNW⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (G := U₀') hW_open h1W
  -- Push `N` forward along the open subtype inclusion `U₀' →* G`.
  let H_sub : Subgroup G := N.toSubgroup.map U₀'.subtype
  have hH_open : IsOpen (H_sub : Set G) := by
    rw [Subgroup.coe_map, Subgroup.coe_subtype]
    exact hU₀'_open.isOpenMap_subtypeVal _ N.toOpenSubgroup.isOpen
  let V : OpenSubgroup G := ⟨H_sub, hH_open⟩
  have hVU₀ : V ≤ U₀ := by
    rintro _ ⟨x, -, rfl⟩
    exact x.property
  have hsub : V.toSubgroup.subgroupOf U₀' = N.toSubgroup := by
    ext x
    simp [V, H_sub, Subgroup.mem_subgroupOf]
  refine ⟨V, hU₀.of_isClosed_subset V.isClosed hVU₀, hVU₀, ?_, ?_⟩
  · rw [hsub]
    exact N.isNormal'
  · rintro _ ⟨x, hxN, rfl⟩
    exact hWs (hNW hxN)

end OpenSubgroup

namespace TauCeti

/-- **Van Dantzig's theorem**, in instance form: a zero-dimensional, weakly locally compact
topological group is nonarchimedean. This covers Hausdorff, totally disconnected, weakly locally
compact groups, which are zero-dimensional, and in particular profinite groups. Every
neighbourhood of the identity contains in fact a compact open subgroup, by
`NonarchimedeanGroup.nhds_one_hasBasis_isCompact_openSubgroup`. -/
@[to_additive IsTopologicalAddGroup.nonarchimedeanAddGroup_of_weaklyLocallyCompactSpace
/-- **Van Dantzig's theorem**, in instance form: a zero-dimensional, weakly locally compact
topological additive group is nonarchimedean. This covers Hausdorff, totally disconnected, weakly
locally compact additive groups, and in particular compact totally disconnected ones. -/]
instance (priority := 100) IsTopologicalGroup.nonarchimedeanGroup_of_weaklyLocallyCompactSpace
    [IsTopologicalGroup G] [ZeroDimensionalSpace G] [WeaklyLocallyCompactSpace G] :
    NonarchimedeanGroup G where
  is_nonarchimedean U hU := by
    obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G)
    obtain ⟨C, ⟨hCc, hC1⟩, hCUK⟩ := (nhds_basis_isClopen (1 : G)).mem_iff.1 (inter_mem hU hK1)
    obtain ⟨H, -, hHC⟩ := (hK.of_isClosed_subset hCc.isClosed (hCUK.trans inter_subset_right))
      |>.exists_openSubgroup_subset hCc.isOpen hC1
    exact ⟨H, hHC.trans (hCUK.trans inter_subset_left)⟩

/-- **Van Dantzig's theorem.** For a Hausdorff topological group `G` the following are
equivalent:
1. `G` is locally compact and totally disconnected;
2. `G` is locally compact and nonarchimedean;
3. every neighbourhood of the identity contains a compact open subgroup.

Such a group is called *locally profinite*. -/
@[to_additive IsTopologicalAddGroup.locallyCompact_totallyDisconnected_tfae
/-- **Van Dantzig's theorem.** For a Hausdorff topological additive group `G` the following are
equivalent:
1. `G` is locally compact and totally disconnected;
2. `G` is locally compact and nonarchimedean;
3. every neighbourhood of zero contains a compact open additive subgroup. -/]
theorem IsTopologicalGroup.locallyCompact_totallyDisconnected_tfae [IsTopologicalGroup G]
    [T2Space G] :
    List.TFAE [LocallyCompactSpace G ∧ TotallyDisconnectedSpace G,
      LocallyCompactSpace G ∧ NonarchimedeanGroup G,
      ∀ U ∈ 𝓝 (1 : G), ∃ H : OpenSubgroup G, IsCompact (H : Set G) ∧ (H : Set G) ⊆ U] := by
  tfae_have 1 → 2 := fun ⟨_, _⟩ ↦ ⟨inferInstance, inferInstance⟩
  tfae_have 2 → 3 := fun ⟨_, _⟩ U hU ↦
    (NonarchimedeanGroup.nhds_one_hasBasis_isCompact_openSubgroup.mem_iff.1 hU)
  tfae_have 3 → 1 := fun h ↦ by
    have : NonarchimedeanGroup G := ⟨fun U hU ↦
      let ⟨H, _, hHU⟩ := h U hU
      ⟨H, hHU⟩⟩
    obtain ⟨H, hH, -⟩ := h univ univ_mem
    exact ⟨hH.locallyCompactSpace_of_mem_nhds_of_group H.mem_nhds_one, inferInstance⟩
  tfae_finish

end TauCeti
