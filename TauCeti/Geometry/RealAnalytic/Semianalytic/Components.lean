/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.Connected.LocallyConnected
public import TauCeti.Geometry.RealAnalytic.Semianalytic.Manifold
import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.Geometry.Manifold.ModelTransport.Boundaryless
import TauCeti.Geometry.RealAnalytic.Semianalytic.Decomposition
import TauCeti.Topology.ConnectedComponents
import TauCeti.Topology.LocallyConnected
import TauCeti.Topology.OpenPartialHomeomorph.Basic

/-!
# Connected components and local connectedness of semianalytic sets

In a finite-dimensional real normed space, the local connected decomposition of a semianalytic germ
(`TauCeti.SemianalyticAt.exists_isConnected_partition_inter`) implies that near any ambient point
where a set `s` is semianalytic — including frontier points and points outside `s` — an arbitrarily
small open semianalytic neighborhood meets only finitely many connected components of `s`, and its
intersection with every connected component of `s` is semianalytic. Consequently:

* every connected component of a semianalytic set is semianalytic
  (`TauCeti.IsSemianalytic.connectedComponentIn`), and pointwise `SemianalyticAt s x` already passes
  to `SemianalyticAt (connectedComponentIn s y) x` (`TauCeti.SemianalyticAt.connectedComponentIn`);
* the distinct nonempty connected components of a semianalytic set form a locally finite family
  (`TauCeti.IsSemianalytic.locallyFinite_connectedComponentIn`), so only finitely many meet any
  compact set (`TauCeti.IsSemianalytic.finite_image_connectedComponentIn_of_isCompact`), and a
  bounded semianalytic set has finitely many connected components
  (`TauCeti.IsSemianalytic.finite_image_connectedComponentIn_of_isBounded`);
* every point of a semianalytic set has a relative neighborhood basis of connected semianalytic
  relatively open subsets (`TauCeti.SemianalyticAt.nhdsWithin_hasBasis_isConnected`), so every
  semianalytic set is locally connected in its subspace topology
  (`TauCeti.IsSemianalytic.locallyConnectedSpace`).

Reading the preferred extended chart on a boundaryless manifold modelled on a finite-dimensional
real normed space transports these local finiteness, component-semianalyticity, and
local-connectedness properties to `TauCeti.MSemianalyticAt` and `TauCeti.IsMSemianalytic` without
requiring smoothness of the atlas or Hausdorffness of the ambient space.

The structure and arguments closely follow the parallel semialgebraic development in
`TauCeti.Geometry.RealAlgebraic.Semialgebraic.Components` and
`TauCeti.Geometry.RealAlgebraic.Semialgebraic.LocallyConnected`, using the general topological
component lemmas `TauCeti.connectedComponentIn_inter_eq_sUnion`,
`Set.Finite.image_connectedComponentIn_sUnion`, `Set.Finite.isOpen_preimage_connectedComponentIn`,
`Set.Finite.isOpen_preimage_connectedComponentIn_inter`,
`Set.Finite.connectedComponentIn_inter_mem_nhdsWithin`,
`TauCeti.locallyFinite_connectedComponentIn_iff`, and
`TauCeti.locallyConnectedSpace_subtype_iff_nhdsWithin`.

## References

* S. Łojasiewicz, *Ensembles semi-analytiques*, IHÉS, 1965, §16–17.
* E. Bierstone and P. D. Milman, *Semianalytic and subanalytic sets*, Publications Mathématiques de
  l'IHÉS 67 (1988), 5–42, Corollary 2.7.
-/

public section

open Filter Set Topology
open scoped Manifold

namespace TauCeti

/-! ### Connected components and local connectedness in normed spaces -/

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Near any ambient point where `s` is semianalytic, all connected components of `s` have
semianalytic intersections with one common, arbitrarily small open semianalytic neighborhood. -/
theorem SemianalyticAt.exists_isSemianalytic_inter_connectedComponentIn {s V : Set E} {x : E}
    (hs : SemianalyticAt s x) (hV : V ∈ 𝓝 x) :
    ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ V ∧ IsSemianalytic U ∧
      ∀ y, IsSemianalytic (_root_.connectedComponentIn s y ∩ U) := by
  obtain ⟨U, 𝒞, hUo, hxU, hUV, hUsa, _, h𝒞fin, _, h𝒞cov, h𝒞cell⟩ :=
    hs.exists_isConnected_partition_inter hV
  refine ⟨U, hUo, hxU, hUV, hUsa, fun y ↦ ?_⟩
  rw [connectedComponentIn_inter_eq_sUnion (fun t ht ↦ (h𝒞cell t ht).1.isPreconnected) h𝒞cov,
    sUnion_eq_biUnion]
  exact .biUnion (h𝒞fin.subset (sep_subset _ _)) fun t ht ↦ (h𝒞cell t ht.1).2.1

/-- Only finitely many connected components of `s` meet a sufficiently small open semianalytic
neighborhood of any ambient point where `s` is semianalytic. -/
theorem SemianalyticAt.exists_finite_image_connectedComponentIn {s V : Set E} {x : E}
    (hs : SemianalyticAt s x) (hV : V ∈ 𝓝 x) :
    ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ V ∧ IsSemianalytic U ∧
      (_root_.connectedComponentIn s '' (s ∩ U)).Finite := by
  obtain ⟨U, 𝒞, hUo, hxU, hUV, hUsa, _, h𝒞fin, _, h𝒞cov, h𝒞cell⟩ :=
    hs.exists_isConnected_partition_inter hV
  refine ⟨U, hUo, hxU, hUV, hUsa, ?_⟩
  rw [← h𝒞cov]
  exact h𝒞fin.image_connectedComponentIn_sUnion (fun t ht ↦ (h𝒞cell t ht).1.isPreconnected)
    (h𝒞cov ▸ inter_subset_left)

/-- If `s` is semianalytic at `x`, then every connected component of `s` is semianalytic at `x`,
including when `x` lies outside `s` or on its frontier. -/
theorem SemianalyticAt.connectedComponentIn {s : Set E} {x : E} (hs : SemianalyticAt s x) (y : E) :
    SemianalyticAt (_root_.connectedComponentIn s y) x := by
  obtain ⟨U, hUo, hxU, -, -, hcomp⟩ := hs.exists_isSemianalytic_inter_connectedComponentIn univ_mem
  refine ((hcomp y).semianalyticAt x).congr ?_
  filter_upwards [hUo.mem_nhds hxU] with z hz
  simp [hz]

/-- Every connected component of a semianalytic set is semianalytic. -/
theorem IsSemianalytic.connectedComponentIn {s : Set E} (hs : IsSemianalytic s) (y : E) :
    IsSemianalytic (_root_.connectedComponentIn s y) :=
  isSemianalytic_iff.2 fun x ↦ (hs.semianalyticAt x).connectedComponentIn y

/-- The distinct nonempty connected components of a semianalytic set form a locally finite family in
the ambient normed space. -/
theorem IsSemianalytic.locallyFinite_connectedComponentIn {s : Set E} (hs : IsSemianalytic s) :
    LocallyFinite (fun C : (_root_.connectedComponentIn s '' s) ↦ (C : Set E)) :=
  locallyFinite_connectedComponentIn_iff.2 fun x ↦ by
    obtain ⟨U, hUo, hxU, -, -, hfin⟩ :=
      (hs.semianalyticAt x).exists_finite_image_connectedComponentIn univ_mem
    exact ⟨U, hUo.mem_nhds hxU, hfin⟩

/-- Only finitely many connected components of a semianalytic set meet a given compact set. -/
theorem IsSemianalytic.finite_image_connectedComponentIn_of_isCompact {s K : Set E}
    (hs : IsSemianalytic s) (hK : IsCompact K) :
    (_root_.connectedComponentIn s '' (s ∩ K)).Finite :=
  hs.locallyFinite_connectedComponentIn.finite_image_connectedComponentIn_of_isCompact hK

/-- A bounded semianalytic subset of a finite-dimensional real normed space has only finitely many
connected components. -/
theorem IsSemianalytic.finite_image_connectedComponentIn_of_isBounded {s : Set E}
    (hs : IsSemianalytic s) (hb : Bornology.IsBounded s) :
    (_root_.connectedComponentIn s '' s).Finite := by
  simpa only [inter_eq_self_of_subset_left subset_closure] using
    hs.finite_image_connectedComponentIn_of_isCompact hb.isCompact_closure

/-- Near any point `x ∈ s` at which `s` is semianalytic, every relative neighborhood of `x` in `s`
contains a connected semianalytic subset open in `s`. -/
theorem SemianalyticAt.exists_isConnected_mem_nhdsWithin {s V : Set E} {x : E}
    (hs : SemianalyticAt s x) (hx : x ∈ s) (hV : V ∈ 𝓝[s] x) :
    ∃ C, C ∈ 𝓝[s] x ∧ C ⊆ s ∩ V ∧ IsConnected C ∧ IsSemianalytic C ∧
      IsOpen ((Subtype.val : s → E) ⁻¹' C) := by
  obtain ⟨W, hW, hWV⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hV
  obtain ⟨U, 𝒞, hUo, hxU, hUW, _, hsUsa, h𝒞fin, _, h𝒞cov, h𝒞cell⟩ :=
    hs.exists_isConnected_partition_inter hW
  have hfin : (_root_.connectedComponentIn (s ∩ U) '' (s ∩ U)).Finite := by
    simpa only [h𝒞cov] using
      h𝒞fin.image_connectedComponentIn_sUnion (fun t ht ↦ (h𝒞cell t ht).1.isPreconnected)
        h𝒞cov.subset
  have hCT := connectedComponentIn_subset (s ∩ U) x
  exact ⟨_root_.connectedComponentIn (s ∩ U) x,
    hfin.connectedComponentIn_inter_mem_nhdsWithin hx (hUo.mem_nhds hxU),
    fun y hy ↦ ⟨(hCT hy).1, hWV ⟨hUW (hCT hy).2, (hCT hy).1⟩⟩,
    isConnected_connectedComponentIn_iff.2 ⟨hx, hxU⟩, hsUsa.connectedComponentIn x,
    hfin.isOpen_preimage_connectedComponentIn_inter hUo x⟩

/-- At any point `x ∈ s` where `s` is semianalytic, `𝓝[s] x` has a basis of connected semianalytic
sets open in the subspace `s`. -/
theorem SemianalyticAt.nhdsWithin_hasBasis_isConnected {s : Set E} {x : E}
    (hs : SemianalyticAt s x) (hx : x ∈ s) :
    (𝓝[s] x).HasBasis
      (fun C : Set E ↦ x ∈ C ∧ C ⊆ s ∧ IsConnected C ∧ IsSemianalytic C ∧
        IsOpen ((Subtype.val : s → E) ⁻¹' C)) id := by
  refine ⟨fun V ↦ ⟨fun hV ↦ ?_, fun ⟨C, ⟨hxC, _, _, _, ho⟩, hCV⟩ ↦ ?_⟩⟩
  · obtain ⟨C, hCn, hCV, hc, hsa, ho⟩ := hs.exists_isConnected_mem_nhdsWithin hx hV
    exact ⟨C, ⟨mem_of_mem_nhdsWithin hx hCn, hCV.trans inter_subset_left, hc, hsa, ho⟩,
      hCV.trans inter_subset_right⟩
  · rw [← map_nhds_subtypeVal (⟨x, hx⟩ : s)]
    exact mem_of_superset (ho.mem_nhds hxC) hCV

/-- Every semianalytic subset of a finite-dimensional real normed space is locally connected in its
subspace topology. -/
theorem IsSemianalytic.locallyConnectedSpace {s : Set E} (hs : IsSemianalytic s) :
    LocallyConnectedSpace s :=
  locallyConnectedSpace_subtype_iff_nhdsWithin.2 fun x hx _ hV ↦ by
    obtain ⟨C, hCn, hCV, hc, _, _⟩ := (hs.semianalyticAt x).exists_isConnected_mem_nhdsWithin hx hV
    exact ⟨C, hCn, hCV, hc.isPreconnected⟩

end NormedSpace

/-! ### Connected components and local connectedness on boundaryless manifolds -/

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- **Local connected partition on a manifold.** If `s` is semianalytic at a manifold point `x` and
`V ∈ 𝓝 x`, there is an open neighborhood `U ⊆ V` of `x` such that `s ∩ U` is partitioned into
finitely many pairwise disjoint connected locally closed subsets, each semianalytic at `x`. -/
theorem MSemianalyticAt.exists_isConnected_partition_inter {s V : Set M} {x : M}
    (hs : MSemianalyticAt I s x) (hV : V ∈ 𝓝 x) :
    ∃ (U : Set M) (𝒞 : Set (Set M)),
      IsOpen U ∧ x ∈ U ∧ U ⊆ V ∧
      𝒞.Finite ∧ 𝒞.PairwiseDisjoint id ∧ ⋃₀ 𝒞 = s ∩ U ∧
      ∀ C ∈ 𝒞, IsConnected C ∧ IsLocallyClosed C ∧ MSemianalyticAt I C x := by
  -- `BoundarylessModel I M` shares carrier and topology with `M` definitionally, so
  -- `BoundarylessModel.chart I (chartAt H x)` has type `OpenPartialHomeomorph M E`.
  let e : OpenPartialHomeomorph M E := BoundarylessModel.chart I (chartAt H x)
  have he_pe : e.toPartialEquiv = extChartAt I x := by
    rw [extChartAt]
    exact BoundarylessModel.chart_toPartialEquiv I (chartAt H x)
  have he : ⇑e = ⇑(extChartAt I x) := by rw [← e.coe_toPartialEquiv, he_pe]
  have he_symm : ⇑e.symm = ⇑(extChartAt I x).symm := by rw [← e.coe_toPartialEquiv_symm, he_pe]
  have hx : x ∈ e.source := by
    rw [he_pe]
    exact mem_extChartAt_source (I := I) x
  have hs' : SemianalyticAt (e.symm ⁻¹' s) (e x) := by
    rw [he, he_symm]
    exact (mSemianalyticAt_def I).1 hs
  have hV₀ : e.target ∩ e.symm ⁻¹' V ∈ 𝓝 (e x) := inter_mem (e.open_target.mem_nhds (e.mapsTo hx))
    ((e.continuousAt_symm (e.mapsTo hx)).preimage_mem_nhds (by rwa [e.left_inv hx]))
  obtain ⟨U₀, 𝒞₀, hU₀o, hexU₀, hU₀sub, _, _, h𝒞₀fin, h𝒞₀disj, h𝒞₀cov, h𝒞₀cell⟩ :=
    hs'.exists_isConnected_partition_inter hV₀
  have hU₀t : U₀ ⊆ e.target := hU₀sub.trans inter_subset_left
  let 𝒞 : Set (Set M) := image e.symm '' 𝒞₀
  refine ⟨e.symm '' U₀, 𝒞, e.isOpen_image_symm_of_subset_target hU₀o hU₀t,
    ⟨e x, hexU₀, e.left_inv hx⟩, image_subset_iff.2 (hU₀sub.trans inter_subset_right),
    h𝒞₀fin.image _, ?_, ?_, ?_⟩
  · rintro _ ⟨C₁, hC₁, rfl⟩ _ ⟨C₂, hC₂, rfl⟩ hne
    have h₁ : C₁ ⊆ e.target :=
      (subset_sUnion_of_mem hC₁).trans (h𝒞₀cov ▸ inter_subset_right.trans hU₀t)
    have h₂ : C₂ ⊆ e.target :=
      (subset_sUnion_of_mem hC₂).trans (h𝒞₀cov ▸ inter_subset_right.trans hU₀t)
    refine disjoint_left.2 fun _ ⟨z₁, hz₁, hz₁eq⟩ ⟨z₂, hz₂, hz₂eq⟩ ↦
      disjoint_left.1 (h𝒞₀disj hC₁ hC₂ fun h ↦ hne (h ▸ rfl)) hz₁ ?_
    exact e.symm.injOn (h₂ hz₂) (h₁ hz₁) (hz₂eq.trans hz₁eq.symm) ▸ hz₂
  · rw [← image_sUnion, h𝒞₀cov, inter_comm, image_inter_preimage, inter_comm]
  · rintro _ ⟨C₀, hC₀, rfl⟩
    have hC₀t : C₀ ⊆ e.target :=
      (subset_sUnion_of_mem hC₀).trans (h𝒞₀cov ▸ inter_subset_right.trans hU₀t)
    refine ⟨(h𝒞₀cell C₀ hC₀).1.image e.symm (e.continuousOn_symm.mono hC₀t),
      e.isLocallyClosed_image_symm_of_subset_target (h𝒞₀cell C₀ hC₀).2.2 hC₀t, ?_⟩
    rw [mSemianalyticAt_def, ← he, ← he_symm]
    refine ((h𝒞₀cell C₀ hC₀).2.1.semianalyticAt (e x)).congr ?_
    filter_upwards [hU₀o.mem_nhds hexU₀] with z hz
    simp only [mem_preimage]
    exact ⟨fun hzC₀ ↦ mem_image_of_mem _ hzC₀,
      fun ⟨w, hwC₀, hwz⟩ ↦ e.symm.injOn (hC₀t hwC₀) (hU₀t hz) hwz ▸ hwC₀⟩

/-- Only finitely many connected components of `s` meet a sufficiently small open neighborhood of
any manifold point where `s` is semianalytic. -/
theorem MSemianalyticAt.exists_finite_image_connectedComponentIn {s V : Set M} {x : M}
    (hs : MSemianalyticAt I s x) (hV : V ∈ 𝓝 x) :
    ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ V ∧ (_root_.connectedComponentIn s '' (s ∩ U)).Finite := by
  obtain ⟨U, 𝒞, hUo, hxU, hUV, h𝒞fin, _, h𝒞cov, h𝒞cell⟩ := hs.exists_isConnected_partition_inter hV
  refine ⟨U, hUo, hxU, hUV, ?_⟩
  rw [← h𝒞cov]
  exact h𝒞fin.image_connectedComponentIn_sUnion (fun t ht ↦ (h𝒞cell t ht).1.isPreconnected)
    (h𝒞cov ▸ inter_subset_left)

/-- If `s` is semianalytic at a manifold point `x`, then every connected component of `s` is
semianalytic at `x`, including when `x` lies outside `s` or on its frontier. -/
theorem MSemianalyticAt.connectedComponentIn {s : Set M} {x : M} (hs : MSemianalyticAt I s x)
    (y : M) : MSemianalyticAt I (_root_.connectedComponentIn s y) x := by
  obtain ⟨U, 𝒞, hUo, hxU, -, h𝒞fin, -, h𝒞cov, h𝒞cell⟩ :=
    hs.exists_isConnected_partition_inter univ_mem
  have hcomp : MSemianalyticAt I (_root_.connectedComponentIn s y ∩ U) x := by
    rw [connectedComponentIn_inter_eq_sUnion (fun t ht ↦ (h𝒞cell t ht).1.isPreconnected) h𝒞cov,
      sUnion_eq_biUnion]
    exact .biUnion (h𝒞fin.subset (sep_subset _ _)) fun t ht ↦ (h𝒞cell t ht.1).2.2
  refine hcomp.congr ?_
  filter_upwards [hUo.mem_nhds hxU] with z hz
  simp [hz]

/-- Every connected component of a semianalytic subset of a manifold is semianalytic. -/
theorem IsMSemianalytic.connectedComponentIn {s : Set M} (hs : IsMSemianalytic I s) (y : M) :
    IsMSemianalytic I (_root_.connectedComponentIn s y) :=
  isMSemianalytic_iff.2 fun x ↦ (hs.mSemianalyticAt x).connectedComponentIn y

/-- The distinct nonempty connected components of a semianalytic subset of a manifold form a locally
finite family. -/
theorem IsMSemianalytic.locallyFinite_connectedComponentIn {s : Set M} (hs : IsMSemianalytic I s) :
    LocallyFinite (fun C : (_root_.connectedComponentIn s '' s) ↦ (C : Set M)) :=
  locallyFinite_connectedComponentIn_iff.2 fun x ↦ by
    obtain ⟨U, hUo, hxU, -, hfin⟩ :=
      (hs.mSemianalyticAt x).exists_finite_image_connectedComponentIn univ_mem
    exact ⟨U, hUo.mem_nhds hxU, hfin⟩

/-- Only finitely many connected components of a semianalytic subset of a manifold meet a given
compact set. -/
theorem IsMSemianalytic.finite_image_connectedComponentIn_of_isCompact {s K : Set M}
    (hs : IsMSemianalytic I s) (hK : IsCompact K) :
    (_root_.connectedComponentIn s '' (s ∩ K)).Finite :=
  hs.locallyFinite_connectedComponentIn.finite_image_connectedComponentIn_of_isCompact hK

/-- On a compact manifold, every semianalytic subset has only finitely many connected components. -/
theorem IsMSemianalytic.finite_image_connectedComponentIn [CompactSpace M] {s : Set M}
    (hs : IsMSemianalytic I s) : (_root_.connectedComponentIn s '' s).Finite := by
  simpa using hs.finite_image_connectedComponentIn_of_isCompact isCompact_univ

/-- Near any point `x ∈ s` at which `s` is semianalytic on a manifold, every relative neighborhood
of `x` in `s` contains a connected subset open in `s`. -/
theorem MSemianalyticAt.exists_isConnected_mem_nhdsWithin {s V : Set M} {x : M}
    (hs : MSemianalyticAt I s x) (hx : x ∈ s) (hV : V ∈ 𝓝[s] x) :
    ∃ C, C ∈ 𝓝[s] x ∧ C ⊆ s ∩ V ∧ IsConnected C ∧ IsOpen ((Subtype.val : s → M) ⁻¹' C) := by
  obtain ⟨W, hW, hWV⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hV
  obtain ⟨U, 𝒞, hUo, hxU, hUW, h𝒞fin, _, h𝒞cov, h𝒞cell⟩ := hs.exists_isConnected_partition_inter hW
  have hfin : (_root_.connectedComponentIn (s ∩ U) '' (s ∩ U)).Finite := by
    simpa only [h𝒞cov] using
      h𝒞fin.image_connectedComponentIn_sUnion (fun t ht ↦ (h𝒞cell t ht).1.isPreconnected)
        h𝒞cov.subset
  have hCT := connectedComponentIn_subset (s ∩ U) x
  exact ⟨_root_.connectedComponentIn (s ∩ U) x,
    hfin.connectedComponentIn_inter_mem_nhdsWithin hx (hUo.mem_nhds hxU),
    fun y hy ↦ ⟨(hCT hy).1, hWV ⟨hUW (hCT hy).2, (hCT hy).1⟩⟩,
    isConnected_connectedComponentIn_iff.2 ⟨hx, hxU⟩,
    hfin.isOpen_preimage_connectedComponentIn_inter hUo x⟩

/-- At any point `x ∈ s` where `s` is semianalytic on a manifold, `𝓝[s] x` has a basis of connected
sets open in the subspace `s`. -/
theorem MSemianalyticAt.nhdsWithin_hasBasis_isConnected {s : Set M} {x : M}
    (hs : MSemianalyticAt I s x) (hx : x ∈ s) :
    (𝓝[s] x).HasBasis
      (fun C : Set M ↦ x ∈ C ∧ C ⊆ s ∧ IsConnected C ∧
        IsOpen ((Subtype.val : s → M) ⁻¹' C)) id := by
  refine ⟨fun V ↦ ⟨fun hV ↦ ?_, fun ⟨C, ⟨hxC, _, _, ho⟩, hCV⟩ ↦ ?_⟩⟩
  · obtain ⟨C, hCn, hCV, hc, ho⟩ := hs.exists_isConnected_mem_nhdsWithin hx hV
    exact ⟨C, ⟨mem_of_mem_nhdsWithin hx hCn, hCV.trans inter_subset_left, hc, ho⟩,
      hCV.trans inter_subset_right⟩
  · rw [← map_nhds_subtypeVal (⟨x, hx⟩ : s)]
    exact mem_of_superset (ho.mem_nhds hxC) hCV

/-- Every semianalytic subset of a boundaryless manifold modelled on a finite-dimensional real
normed space is locally connected in its subspace topology. -/
theorem IsMSemianalytic.locallyConnectedSpace {s : Set M} (hs : IsMSemianalytic I s) :
    LocallyConnectedSpace s :=
  locallyConnectedSpace_subtype_iff_nhdsWithin.2 fun x hx _ hV ↦ by
    obtain ⟨C, hCn, hCV, hc, _⟩ := (hs.mSemianalyticAt x).exists_isConnected_mem_nhdsWithin hx hV
    exact ⟨C, hCn, hCV, hc.isPreconnected⟩

end Manifold

end TauCeti
