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
import Mathlib.Topology.Compactness.LocallyFinite
import TauCeti.Geometry.RealAnalytic.Semianalytic.Decomposition
import TauCeti.Topology.ConnectedComponents

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

## References

* S. Łojasiewicz, *Ensembles semi-analytiques*, IHÉS, 1965, §16–17.
* E. Bierstone and P. D. Milman, *Semianalytic and subanalytic sets*, Publications Mathématiques de
  l'IHÉS 67 (1988), 5–42, Corollary 2.7.
-/

public section

open Filter Set Topology
open scoped Manifold

namespace TauCeti

/-! ### Locally finite unions on charted spaces -/

section LocallyFiniteUnion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- A finite bounded union of sets semianalytic at a manifold point is semianalytic there. -/
theorem MSemianalyticAt.biUnion {ι : Type*} {J : Set ι} (hJ : J.Finite) {s : ι → Set M} {x : M}
    (hs : ∀ i ∈ J, MSemianalyticAt I (s i) x) : MSemianalyticAt I (⋃ i ∈ J, s i) x := by
  have := hJ.to_subtype
  simpa only [biUnion_eq_iUnion] using MSemianalyticAt.iUnion fun i : J ↦ hs i.1 i.2

/-- A finite bounded union of semianalytic subsets of a manifold is semianalytic. -/
protected theorem IsMSemianalytic.biUnion {ι : Type*} {J : Set ι} (hJ : J.Finite) {s : ι → Set M}
    (hs : ∀ i ∈ J, IsMSemianalytic I (s i)) : IsMSemianalytic I (⋃ i ∈ J, s i) :=
  isMSemianalytic_iff.2 fun x ↦ .biUnion hJ fun i hi ↦ (hs i hi).mSemianalyticAt x

/-- **Locally finite unions on manifolds.** The union of a locally finite family of semianalytic
subsets of a charted space is semianalytic. -/
theorem _root_.LocallyFinite.isMSemianalytic_iUnion {ι : Type*} {s : ι → Set M}
    (hfin : LocallyFinite s) (hs : ∀ i, IsMSemianalytic I (s i)) :
    IsMSemianalytic I (⋃ i, s i) :=
  isMSemianalytic_iff.2 fun x ↦ by
    obtain ⟨V, hV, hJ⟩ := hfin x
    refine (MSemianalyticAt.biUnion hJ fun i _ ↦ (hs i).mSemianalyticAt x).congr ?_
    filter_upwards [hV] with y hy
    simp only [mem_iUnion, exists_prop]
    exact ⟨fun ⟨i, _, hyi⟩ ↦ ⟨i, hyi⟩, fun ⟨i, hyi⟩ ↦ ⟨i, ⟨y, hyi, hy⟩, hyi⟩⟩

end LocallyFiniteUnion

/-! ### Topological helpers for locally finite connected decompositions -/

section TopologicalHelpers

variable {X : Type*} [TopologicalSpace X]

private theorem locallyFinite_connectedComponentIn_of_forall {s : Set X}
    (h : ∀ x, ∃ U, IsOpen U ∧ x ∈ U ∧ (_root_.connectedComponentIn s '' (s ∩ U)).Finite) :
    LocallyFinite (fun C : (_root_.connectedComponentIn s '' s) ↦ (C : Set X)) := by
  intro x
  obtain ⟨U, hUo, hxU, hfin⟩ := h x
  refine ⟨U, hUo.mem_nhds hxU, (hfin.preimage Subtype.val_injective.injOn).subset ?_⟩
  rintro C ⟨y, hyC, hyU⟩
  obtain ⟨z, _, hzC⟩ := C.property
  have hy : y ∈ _root_.connectedComponentIn s z := hzC ▸ hyC
  exact ⟨y, ⟨connectedComponentIn_subset s z hy, hyU⟩, (connectedComponentIn_eq hy).symm.trans hzC⟩

private theorem finite_image_connectedComponentIn_of_locallyFinite {s K : Set X}
    (hlf : LocallyFinite (fun C : (_root_.connectedComponentIn s '' s) ↦ (C : Set X)))
    (hK : IsCompact K) :
    (_root_.connectedComponentIn s '' (s ∩ K)).Finite := by
  refine ((hlf.finite_nonempty_inter_compact hK).image Subtype.val).subset ?_
  rintro _ ⟨x, ⟨hxs, hxK⟩, rfl⟩
  exact ⟨⟨_root_.connectedComponentIn s x, x, hxs, rfl⟩,
    ⟨x, mem_connectedComponentIn hxs, hxK⟩, rfl⟩

private theorem nhdsWithin_connectedComponentIn_inter {s U : Set X} {𝒞 : Set (Set X)} {x : X}
    (hx : x ∈ s) (hUo : IsOpen U) (hxU : x ∈ U) (h𝒞fin : 𝒞.Finite) (h𝒞cov : ⋃₀ 𝒞 = s ∩ U)
    (h𝒞conn : ∀ t ∈ 𝒞, IsPreconnected t) :
    _root_.connectedComponentIn (s ∩ U) x ∈ 𝓝[s] x ∧
      IsOpen ((Subtype.val : s → X) ⁻¹' _root_.connectedComponentIn (s ∩ U) x) := by
  set C := _root_.connectedComponentIn (s ∩ U) x
  have hxC : x ∈ C := mem_connectedComponentIn ⟨hx, hxU⟩
  have hCT : C ⊆ s ∩ U := connectedComponentIn_subset _ _
  have hfin : (_root_.connectedComponentIn (s ∩ U) '' (s ∩ U)).Finite := by
    simpa only [h𝒞cov] using h𝒞fin.image_connectedComponentIn_sUnion h𝒞conn h𝒞cov.subset
  obtain ⟨O, hOo, hO⟩ := isOpen_induced_iff.1 (hfin.isOpen_preimage_connectedComponentIn x)
  have hCeq : C = s ∩ (U ∩ O) := by
    apply Set.eq_of_preimage_val_eq_of_subset hCT (by grind)
    simpa only [← inter_assoc, Subtype.preimage_coe_self_inter] using hO.symm
  refine ⟨by rw [hCeq]; exact inter_mem_nhdsWithin s ((hUo.inter hOo).mem_nhds (hCeq ▸ hxC).2), ?_⟩
  rw [hCeq, preimage_inter]
  simpa only [Subtype.coe_preimage_self, univ_inter] using
    (hUo.inter hOo).preimage continuous_subtype_val

private theorem locallyConnectedSpace_of_forall {s : Set X}
    (h : ∀ x ∈ s, ∀ V ∈ 𝓝[s] x, ∃ C ∈ 𝓝[s] x, C ⊆ s ∩ V ∧ IsConnected C) :
    LocallyConnectedSpace s := by
  refine locallyConnectedSpace_iff_connected_subsets.2 fun x V hV ↦ ?_
  obtain ⟨W, hW, hWV⟩ := (mem_nhds_subtype s x V).1 hV
  obtain ⟨C, hCn, hCW, hc⟩ := h x x.property W (mem_nhdsWithin_of_mem_nhds hW)
  refine ⟨(Subtype.val : s → X) ⁻¹' C, ?_, ?_, fun y hy ↦ hWV (hCW hy).2⟩
  · rw [nhds_subtype_eq_comap_nhdsWithin]
    exact preimage_mem_comap hCn
  · apply Topology.IsInducing.subtypeVal.isPreconnected_image.1
    simpa only [Subtype.image_preimage_val, inter_eq_right.2 (hCW.trans inter_subset_left)] using
      hc.isPreconnected

end TopologicalHelpers

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
  locallyFinite_connectedComponentIn_of_forall fun x ↦ by
    obtain ⟨U, hUo, hxU, -, -, hfin⟩ :=
      (hs.semianalyticAt x).exists_finite_image_connectedComponentIn univ_mem
    exact ⟨U, hUo, hxU, hfin⟩

/-- Only finitely many connected components of a semianalytic set meet a given compact set. -/
theorem IsSemianalytic.finite_image_connectedComponentIn_of_isCompact {s K : Set E}
    (hs : IsSemianalytic s) (hK : IsCompact K) :
    (_root_.connectedComponentIn s '' (s ∩ K)).Finite :=
  finite_image_connectedComponentIn_of_locallyFinite hs.locallyFinite_connectedComponentIn hK

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
  obtain ⟨hCn, hopen⟩ := nhdsWithin_connectedComponentIn_inter hx hUo hxU h𝒞fin h𝒞cov
    fun t ht ↦ (h𝒞cell t ht).1.isPreconnected
  have hCT := connectedComponentIn_subset (s ∩ U) x
  exact ⟨_root_.connectedComponentIn (s ∩ U) x, hCn,
    fun y hy ↦ ⟨(hCT hy).1, hWV ⟨hUW (hCT hy).2, (hCT hy).1⟩⟩,
    isConnected_connectedComponentIn_iff.2 ⟨hx, hxU⟩, hsUsa.connectedComponentIn x, hopen⟩

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
  · rw [← map_nhds_subtype_val (⟨x, hx⟩ : s)]
    exact mem_of_superset (ho.mem_nhds hxC) hCV

/-- Every semianalytic subset of a finite-dimensional real normed space is locally connected in its
subspace topology. -/
theorem IsSemianalytic.locallyConnectedSpace {s : Set E} (hs : IsSemianalytic s) :
    LocallyConnectedSpace s :=
  locallyConnectedSpace_of_forall fun x hx _ hV ↦ by
    obtain ⟨C, hCn, hCV, hc, _, _⟩ := (hs.semianalyticAt x).exists_isConnected_mem_nhdsWithin hx hV
    exact ⟨C, hCn, hCV, hc⟩

end NormedSpace

/-! ### Connected components and local connectedness on boundaryless manifolds -/

section Manifold

private theorem _root_.OpenPartialHomeomorph.isLocallyClosed_image_symm_of_subset_target
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : OpenPartialHomeomorph X Y)
    {s : Set Y} (hs : IsLocallyClosed s) (hst : s ⊆ e.target) :
    IsLocallyClosed (e.symm '' s) := by
  obtain ⟨O, F, hO, hF, rfl⟩ := hs
  refine ⟨e.symm '' (e.target ∩ O), (e.symm '' (e.target ∩ O ∩ Fᶜ))ᶜ,
    e.isOpen_image_symm_of_subset_target (e.open_target.inter hO) inter_subset_left,
    (e.isOpen_image_symm_of_subset_target ((e.open_target.inter hO).inter hF.isOpen_compl)
      (inter_subset_left.trans inter_subset_left)).isClosed_compl, ?_⟩
  ext x
  simp only [mem_image, mem_inter_iff, mem_compl_iff, not_exists, not_and]
  refine ⟨?_, ?_⟩
  · rintro ⟨z, ⟨hzO, hzF⟩, rfl⟩
    have hzt : z ∈ e.target := hst ⟨hzO, hzF⟩
    exact ⟨⟨z, ⟨hzt, hzO⟩, rfl⟩, fun w ⟨⟨hwt, _⟩, hwF⟩ hwz ↦
      hwF (e.symm.injOn hwt hzt hwz ▸ hzF)⟩
  · rintro ⟨⟨z, ⟨hzt, hzO⟩, rfl⟩, hnot⟩
    exact ⟨z, ⟨hzO, by_contra fun hzF ↦ hnot z ⟨⟨hzt, hzO⟩, hzF⟩ rfl⟩, rfl⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- **Local connected partition on a manifold.** If `s` is semianalytic at a manifold point `x` and
`V ∈ 𝓝 x`, there is an open neighborhood `U ⊆ V` of `x` such that `s ∩ U` is partitioned into
finitely many pairwise disjoint connected locally closed subsets. -/
theorem MSemianalyticAt.exists_isConnected_partition_inter {s V : Set M} {x : M}
    (hs : MSemianalyticAt I s x) (hV : V ∈ 𝓝 x) :
    ∃ (U : Set M) (𝒞 : Set (Set M)),
      IsOpen U ∧ x ∈ U ∧ U ⊆ V ∧
      𝒞.Finite ∧ 𝒞.PairwiseDisjoint id ∧ ⋃₀ 𝒞 = s ∩ U ∧
      ∀ C ∈ 𝒞, IsConnected C ∧ IsLocallyClosed C := by
  let e : OpenPartialHomeomorph M E := (chartAt H x).trans I.toHomeomorph.toOpenPartialHomeomorph
  have hx : x ∈ e.source := by simp [e, mem_chart_source]
  have hs' : SemianalyticAt (e.symm ⁻¹' s) (e x) := (mSemianalyticAt_def I).1 hs
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
    exact ⟨(h𝒞₀cell C₀ hC₀).1.image e.symm (e.continuousOn_symm.mono hC₀t),
      e.isLocallyClosed_image_symm_of_subset_target (h𝒞₀cell C₀ hC₀).2.2 hC₀t⟩

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
  let e : OpenPartialHomeomorph M E := (chartAt H x).trans I.toHomeomorph.toOpenPartialHomeomorph
  have hx : x ∈ e.source := by simp [e, mem_chart_source]
  have hs' : SemianalyticAt (e.symm ⁻¹' s) (e x) := (mSemianalyticAt_def I).1 hs
  obtain ⟨U₀, 𝒞₀, hU₀o, hexU₀, hU₀t, _, _, h𝒞₀fin, _, h𝒞₀cov, h𝒞₀cell⟩ :=
    hs'.exists_isConnected_partition_inter (e.open_target.mem_nhds (e.mapsTo hx))
  let 𝒞 : Set (Set M) := image e.symm '' 𝒞₀
  have hC₀sub {C₀ : Set E} (hC₀ : C₀ ∈ 𝒞₀) : C₀ ⊆ U₀ :=
    (subset_sUnion_of_mem hC₀).trans (h𝒞₀cov ▸ inter_subset_right)
  have h𝒞cov : ⋃₀ 𝒞 = s ∩ (e.symm '' U₀) := by
    rw [← image_sUnion, h𝒞₀cov, inter_comm, image_inter_preimage, inter_comm]
  have h𝒞conn : ∀ C ∈ 𝒞, IsPreconnected C := by
    rintro _ ⟨C₀, hC₀, rfl⟩
    exact (h𝒞₀cell C₀ hC₀).1.isPreconnected.image e.symm
      (e.continuousOn_symm.mono ((hC₀sub hC₀).trans hU₀t))
  have hcomp := connectedComponentIn_inter_eq_sUnion h𝒞conn h𝒞cov y
  let ℐ : Set (Set E) := {C₀ ∈ 𝒞₀ | e.symm '' C₀ ⊆ _root_.connectedComponentIn s y}
  have hpre : e.symm ⁻¹' _root_.connectedComponentIn s y ∩ U₀ = ⋃ C₀ ∈ ℐ, C₀ := by
    ext z
    simp only [ℐ, mem_inter_iff, mem_preimage, mem_iUnion, mem_sep_iff, exists_prop]
    refine ⟨fun ⟨hzs, hzU₀⟩ ↦ ?_, fun ⟨C₀, ⟨hC₀, hC₀y⟩, hzC₀⟩ ↦
      ⟨hC₀y (mem_image_of_mem _ hzC₀), hC₀sub hC₀ hzC₀⟩⟩
    have hzmem : e.symm z ∈ _root_.connectedComponentIn s y ∩ (e.symm '' U₀) :=
      ⟨hzs, mem_image_of_mem _ hzU₀⟩
    obtain ⟨_, ⟨⟨C₀, hC₀, rfl⟩, hC₀y⟩, w, hwC₀, hwz⟩ := mem_sUnion.1 (hcomp ▸ hzmem)
    exact ⟨C₀, ⟨hC₀, hC₀y⟩, e.symm.injOn (hU₀t (hC₀sub hC₀ hwC₀)) (hU₀t hzU₀) hwz ▸ hwC₀⟩
  have hsa : IsSemianalytic (e.symm ⁻¹' _root_.connectedComponentIn s y ∩ U₀) := by
    rw [hpre]
    exact .biUnion (h𝒞₀fin.subset (sep_subset _ _)) fun C₀ hC₀ ↦ (h𝒞₀cell C₀ hC₀.1).2.1
  refine (mSemianalyticAt_def I).2 ((hsa.semianalyticAt (e x)).congr ?_)
  filter_upwards [hU₀o.mem_nhds hexU₀] with z hz
  simp [e, hz]

/-- Every connected component of a semianalytic subset of a manifold is semianalytic. -/
theorem IsMSemianalytic.connectedComponentIn {s : Set M} (hs : IsMSemianalytic I s) (y : M) :
    IsMSemianalytic I (_root_.connectedComponentIn s y) :=
  isMSemianalytic_iff.2 fun x ↦ (hs.mSemianalyticAt x).connectedComponentIn y

/-- The distinct nonempty connected components of a semianalytic subset of a manifold form a locally
finite family. -/
theorem IsMSemianalytic.locallyFinite_connectedComponentIn {s : Set M} (hs : IsMSemianalytic I s) :
    LocallyFinite (fun C : (_root_.connectedComponentIn s '' s) ↦ (C : Set M)) :=
  locallyFinite_connectedComponentIn_of_forall fun x ↦ by
    obtain ⟨U, hUo, hxU, -, hfin⟩ :=
      (hs.mSemianalyticAt x).exists_finite_image_connectedComponentIn univ_mem
    exact ⟨U, hUo, hxU, hfin⟩

/-- Only finitely many connected components of a semianalytic subset of a manifold meet a given
compact set. -/
theorem IsMSemianalytic.finite_image_connectedComponentIn_of_isCompact {s K : Set M}
    (hs : IsMSemianalytic I s) (hK : IsCompact K) :
    (_root_.connectedComponentIn s '' (s ∩ K)).Finite :=
  finite_image_connectedComponentIn_of_locallyFinite hs.locallyFinite_connectedComponentIn hK

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
  obtain ⟨hCn, hopen⟩ := nhdsWithin_connectedComponentIn_inter hx hUo hxU h𝒞fin h𝒞cov
    fun t ht ↦ (h𝒞cell t ht).1.isPreconnected
  have hCT := connectedComponentIn_subset (s ∩ U) x
  exact ⟨_root_.connectedComponentIn (s ∩ U) x, hCn,
    fun y hy ↦ ⟨(hCT hy).1, hWV ⟨hUW (hCT hy).2, (hCT hy).1⟩⟩,
    isConnected_connectedComponentIn_iff.2 ⟨hx, hxU⟩, hopen⟩

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
  · rw [← map_nhds_subtype_val (⟨x, hx⟩ : s)]
    exact mem_of_superset (ho.mem_nhds hxC) hCV

/-- Every semianalytic subset of a boundaryless manifold modelled on a finite-dimensional real
normed space is locally connected in its subspace topology. -/
theorem IsMSemianalytic.locallyConnectedSpace {s : Set M} (hs : IsMSemianalytic I s) :
    LocallyConnectedSpace s :=
  locallyConnectedSpace_of_forall fun x hx _ hV ↦ by
    obtain ⟨C, hCn, hCV, hc, _⟩ := (hs.mSemianalyticAt x).exists_isConnected_mem_nhdsWithin hx hV
    exact ⟨C, hCn, hCV, hc⟩

end Manifold

end TauCeti
