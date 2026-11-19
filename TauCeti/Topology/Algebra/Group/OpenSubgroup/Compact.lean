/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Pointwise.Stabilizer
public import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
public import Mathlib.Topology.Separation.Regular

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
* `OpenSubgroup.directedOn_isCompact`: the compact open subgroups are directed under reverse
  inclusion.
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
