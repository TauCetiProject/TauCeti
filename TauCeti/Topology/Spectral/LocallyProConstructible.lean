/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Spectral.LocallySpectral
public import TauCeti.Topology.Spectral.ProConstructible
import Mathlib.Topology.LocalAtTarget

/-!
# Locally pro-constructible subsets

On a locally spectral space, pro-constructibility is tested on spectral open subspaces.
This local condition agrees with pro-constructibility on spectral spaces, but does not impose
compactness on a subset of a noncompact space.

A quasi-compact locally spectral map carries locally pro-constructible subsets to locally
pro-constructible subsets. Over a spectral open in the target, compactness gives finitely many
spectral source charts; the spectral image theorem applies on each chart. This is the image
criterion used when deducing closedness from specialization stability in adic geometry.

## References

* R. Huber, *Étale Cohomology of Rigid Analytic Varieties and Adic Spaces*, (1.1.13).
* P. Scholze, *Étale cohomology of diamonds*, §2.
-/

public section

namespace TauCeti

open Set Topology TopologicalSpace

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X}

/-- A subset is locally pro-constructible if its trace on every spectral open subspace is
pro-constructible. On locally spectral spaces these opens cover the space. -/
def IsLocallyProConstructible (s : Set X) : Prop :=
  ∀ U : Set X, IsOpen U → SpectralSpace U →
    IsProConstructible ((Subtype.val : U → X) ⁻¹' s)

/-- Pro-constructible traces on every spectral open imply local pro-constructibility. -/
theorem IsLocallyProConstructible.of_forall
    (hs : ∀ U : Set X, IsOpen U → SpectralSpace U →
      IsProConstructible ((Subtype.val : U → X) ⁻¹' s)) :
    IsLocallyProConstructible s :=
  hs

/-- The trace of a locally pro-constructible subset on a spectral open is pro-constructible. -/
theorem IsLocallyProConstructible.isProConstructible_preimage
    (hs : IsLocallyProConstructible s) {U : Set X} (hU : IsOpen U) [SpectralSpace U] :
    IsProConstructible ((Subtype.val : U → X) ⁻¹' s) :=
  hs U hU inferInstance

/-- On a quasiseparated space, a pro-constructible subset is locally pro-constructible. -/
theorem IsProConstructible.isLocallyProConstructible [QuasiSeparatedSpace X]
    (hs : IsProConstructible s) : IsLocallyProConstructible s := by
  intro U hU hUs
  have := hUs
  exact hs.preimage hU.isOpenEmbedding_subtypeVal.isSpectralMap

/-- On a spectral space the local and global notions of pro-constructibility agree. -/
@[simp]
theorem isLocallyProConstructible_iff_isProConstructible [SpectralSpace X] :
    IsLocallyProConstructible s ↔ IsProConstructible s := by
  refine ⟨fun hs ↦ ?_, IsProConstructible.isLocallyProConstructible⟩
  have := spectralSpace_univ (X := X)
  have h := hs.isProConstructible_preimage (U := univ) isOpen_univ
  simpa using h.image (isOpen_univ.isOpenEmbedding_subtypeVal.isSpectralMap)

@[simp]
theorem isLocallyProConstructible_empty : IsLocallyProConstructible (∅ : Set X) := by
  intro U _ _
  simp

@[simp]
theorem isLocallyProConstructible_univ : IsLocallyProConstructible (univ : Set X) := by
  intro U _ _
  simp

/-- Finite unions preserve local pro-constructibility. -/
theorem IsLocallyProConstructible.union (hs : IsLocallyProConstructible s)
    (ht : IsLocallyProConstructible t) : IsLocallyProConstructible (s ∪ t) := by
  intro U hU hUs
  exact (hs U hU hUs).union (ht U hU hUs)

/-- Intersections preserve local pro-constructibility. -/
theorem IsLocallyProConstructible.inter (hs : IsLocallyProConstructible s)
    (ht : IsLocallyProConstructible t) : IsLocallyProConstructible (s ∩ t) := by
  intro U hU hUs
  exact (hs U hU hUs).inter (ht U hU hUs)

/-- Arbitrary indexed intersections preserve local pro-constructibility. -/
theorem IsLocallyProConstructible.iInter {ι : Sort*} {f : ι → Set X}
    (hf : ∀ i, IsLocallyProConstructible (f i)) : IsLocallyProConstructible (⋂ i, f i) := by
  intro U hU hUs
  rw [preimage_iInter]
  exact IsProConstructible.iInter fun i ↦ hf i U hU hUs

/-- Bounded intersections preserve local pro-constructibility. -/
theorem IsLocallyProConstructible.biInter {ι : Sort*} {p : ι → Prop} {f : ∀ i, p i → Set X}
    (hf : ∀ i hi, IsLocallyProConstructible (f i hi)) :
    IsLocallyProConstructible (⋂ i, ⋂ hi, f i hi) :=
  .iInter fun i ↦ .iInter (hf i)

/-- Arbitrary intersections of a set of locally pro-constructible subsets are locally
pro-constructible. -/
theorem IsLocallyProConstructible.sInter {S : Set (Set X)}
    (hS : ∀ s ∈ S, IsLocallyProConstructible s) : IsLocallyProConstructible (⋂₀ S) := by
  rw [sInter_eq_iInter]
  exact .iInter fun s ↦ hS s.1 s.2

/-- Finite indexed unions preserve local pro-constructibility. -/
theorem IsLocallyProConstructible.iUnion {ι : Type*} [Finite ι] {f : ι → Set X}
    (hf : ∀ i, IsLocallyProConstructible (f i)) : IsLocallyProConstructible (⋃ i, f i) := by
  intro U hU hUs
  rw [preimage_iUnion]
  exact IsProConstructible.iUnion fun i ↦ hf i U hU hUs

/-- Unions over a finite set preserve local pro-constructibility. -/
theorem _root_.Set.Finite.isLocallyProConstructible_biUnion {ι : Type*} {I : Set ι}
    {f : ι → Set X} (hI : I.Finite) (hf : ∀ i ∈ I, IsLocallyProConstructible (f i)) :
    IsLocallyProConstructible (⋃ i ∈ I, f i) := by
  intro U hU hUs
  simp only [preimage_iUnion]
  exact hI.isProConstructible_biUnion fun i hi ↦ hf i hi U hU hUs

/-- Local pro-constructibility can be tested on any cover by spectral open subspaces. -/
theorem IsLocallyProConstructible.of_isOpenCover {ι : Type*} {U : ι → Opens X}
    (hU : IsOpenCover U) [∀ i, SpectralSpace (U i)]
    (hs : ∀ i, IsProConstructible ((Subtype.val : U i → X) ⁻¹' s)) :
    IsLocallyProConstructible s := by
  intro V hVo hVs
  have := hVs
  have hcharts (x : V) : ∃ (i : ι) (W : Set X), W ⊆ V ∩ U i ∧ IsOpen W ∧
      x.1 ∈ W ∧ SpectralSpace W := by
    obtain ⟨i, hxi⟩ := hU.exists_mem x.1
    obtain ⟨W, hWsub, hWo, hxW, -, hWs⟩ :=
      hVo.exists_spectralSpace_subset_inter hVs (U i).isOpen x.2 hxi
    exact ⟨i, W, hWsub, hWo, hxW, hWs⟩
  choose i W hWsub hWo hxW hWs using hcharts
  let g (x : V) : W x → U (i x) := inclusion ((hWsub x).trans inter_subset_right)
  let e (x : V) : W x → V := inclusion ((hWsub x).trans inter_subset_left)
  have himage (x : V) : IsProConstructible (e x '' (Subtype.val ⁻¹' s)) := by
    have := hWs x
    have hg : IsOpenEmbedding (g x) :=
      .inclusion _ ((hWo x).preimage continuous_subtype_val)
    have he : IsOpenEmbedding (e x) :=
      .inclusion _ ((hWo x).preimage continuous_subtype_val)
    exact ((hs (i x)).preimage hg.isSpectralMap).image he.isSpectralMap
  obtain ⟨T, hT⟩ := (isCompact_iff_compactSpace.mpr hVs.toCompactSpace).elim_finite_subcover
    W hWo (fun x hx ↦ mem_iUnion.mpr ⟨⟨x, hx⟩, hxW ⟨x, hx⟩⟩)
  have heq : (Subtype.val : V → X) ⁻¹' s =
      ⋃ x ∈ T, e x '' (Subtype.val ⁻¹' s) := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hxT, hyW⟩ := mem_iUnion₂.mp (hT y.2)
      exact mem_iUnion₂.mpr ⟨x, hxT, ⟨⟨y.1, hyW⟩, hy, Subtype.ext rfl⟩⟩
    · intro hy
      obtain ⟨x, -, z, hz, hzy⟩ := mem_iUnion₂.mp hy
      have : e x z ∈ (Subtype.val : V → X) ⁻¹' s := hz
      exact hzy ▸ this
  rw [heq]
  exact T.finite_toSet.isProConstructible_biUnion fun x _ ↦ himage x

/-- Closed subsets are locally pro-constructible, without any ambient separation hypothesis. -/
theorem _root_.IsClosed.isLocallyProConstructible (hs : IsClosed s) :
    IsLocallyProConstructible s := by
  intro U _ hUs
  have := hUs
  exact (hs.preimage continuous_subtype_val).isProConstructible

/-- A locally pro-constructible subset of a locally spectral space is closed exactly when it
is stable under specialization. -/
theorem IsLocallyProConstructible.isClosed_iff_stableUnderSpecialization
    (hs : IsLocallyProConstructible s) (hX : IsLocallySpectralSpace X) :
    IsClosed s ↔ StableUnderSpecialization s := by
  refine ⟨IsClosed.stableUnderSpecialization, fun hstable ↦ ?_⟩
  have hU : IsOpenCover (fun U : {U : Opens X // SpectralSpace U} ↦ U.1) :=
    IsOpenCover.of_sets (fun U ↦ U.1.isOpen) <| eq_univ_iff_forall.mpr fun x ↦ by
      obtain ⟨U, hUo, hxU, hUs⟩ := isLocallySpectralSpace_iff.mp hX x
      exact mem_iUnion.mpr ⟨⟨⟨U, hUo⟩, hUs⟩, hxU⟩
  rw [hU.isClosed_iff_coe_preimage]
  rintro ⟨U, hUs⟩
  have := hUs
  exact (hs.isProConstructible_preimage U.isOpen).isClosed_iff_stableUnderSpecialization.mpr
    (hstable.preimage continuous_subtype_val)

/-- **Images under quasi-compact locally spectral maps are locally pro-constructible.**
Quasi-compactness is expressed by Mathlib's `IsSpectralMap`: compact open subsets have compact
inverse images. No global compactness or quasiseparatedness of either space is assumed. -/
theorem IsLocallyProConstructible.image (hs : IsLocallyProConstructible s)
    (hX : IsLocallySpectralSpace X) {f : X → Y} (hf : IsLocallySpectralMap f)
    (hqc : IsSpectralMap f) : IsLocallyProConstructible (f '' s) := by
  intro V hVo hVs
  have := hVs
  let C : Set (Set X) := {U | IsOpen U ∧ SpectralSpace U ∧ U ⊆ f ⁻¹' V}
  have hcover : f ⁻¹' V ⊆ ⋃ U ∈ C, U := by
    intro x hx
    obtain ⟨U, ⟨hUo, hUs⟩, hxU, hUV⟩ := hX.isTopologicalBasis.exists_subset_of_mem_open
      hx (hVo.preimage hf.continuous)
    exact mem_iUnion₂.mpr ⟨U, ⟨hUo, hUs, hUV⟩, hxU⟩
  have hVc : IsCompact V := isCompact_iff_compactSpace.mpr hVs.toCompactSpace
  obtain ⟨T, hTC, hTf, hT⟩ :=
    (hqc.isCompact_preimage_of_isOpen hVo hVc).elim_finite_subcover_image (b := C) (c := id)
      (fun U hU ↦ hU.1) hcover
  let g (U : T) : U.1 → V := MapsTo.restrict f U.1 V (hTC U.2).2.2
  have himage (U : T) : IsProConstructible (g U '' (Subtype.val ⁻¹' s)) := by
    have := (hTC U.2).2.1
    exact (hs.isProConstructible_preimage (hTC U.2).1).image
      (hf.isSpectralMap_restrict (hTC U.2).2.2 (hTC U.2).1 hVo)
  have heq : (Subtype.val : V → Y) ⁻¹' (f '' s) =
      ⋃ U : T, g U '' (Subtype.val ⁻¹' s) := by
    ext y
    constructor
    · rintro ⟨x, hxs, hxy⟩
      obtain ⟨U, hUT, hxU⟩ := mem_iUnion₂.mp (hT (hxy ▸ y.2))
      exact mem_iUnion.mpr ⟨⟨U, hUT⟩, ⟨x, hxU⟩, hxs, Subtype.ext hxy⟩
    · intro hy
      obtain ⟨U, x, hxs, hxy⟩ := mem_iUnion.mp hy
      exact ⟨x, hxs, congrArg Subtype.val hxy⟩
  rw [heq]
  have := hTf.to_subtype
  exact IsProConstructible.iUnion himage

/-- A quasi-compact locally spectral map between locally spectral spaces is closed if and only
if it lifts specializations. This is the topological closedness criterion used in properness. -/
theorem IsLocallySpectralMap.isClosedMap_iff_specializingMap {f : X → Y}
    (hf : IsLocallySpectralMap f) (hX : IsLocallySpectralSpace X)
    (hY : IsLocallySpectralSpace Y) (hqc : IsSpectralMap f) :
    IsClosedMap f ↔ SpecializingMap f := by
  refine ⟨IsClosedMap.specializingMap, fun hspec s hs ↦ ?_⟩
  have himage := hs.isLocallyProConstructible.image hX hf hqc
  exact (himage.isClosed_iff_stableUnderSpecialization hY).mpr
    (hs.stableUnderSpecialization.image hspec)

end TauCeti
