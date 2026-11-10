/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Spectral.LocallySpectral
public import TauCeti.Topology.Spectral.ProConstructible

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

open Set Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X}

/-- A subset is locally pro-constructible if its trace on every spectral open subspace is
pro-constructible. On locally spectral spaces these opens cover the space. -/
def IsLocallyProConstructible (s : Set X) : Prop :=
  ∀ U : Set X, IsOpen U → SpectralSpace U →
    IsProConstructible ((Subtype.val : U → X) ⁻¹' s)

/-- Local pro-constructibility is tested on all spectral open subspaces. -/
theorem isLocallyProConstructible_iff_forall :
    IsLocallyProConstructible s ↔ ∀ U : Set X, IsOpen U → SpectralSpace U →
      IsProConstructible ((Subtype.val : U → X) ⁻¹' s) :=
  Iff.rfl

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
theorem isLocallyProConstructible_iff [SpectralSpace X] :
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
  rw [← isOpen_compl_iff]
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨U, hUo, hxU, hUs⟩ := isLocallySpectralSpace_iff.mp hX x
  have := hUs
  have hclosed : IsClosed ((Subtype.val : U → X) ⁻¹' s) :=
    (hs.isProConstructible_preimage hUo).isClosed_iff_stableUnderSpecialization.mpr
      (hstable.preimage continuous_subtype_val)
  have hopen := hUo.isOpenMap_subtype_val _ hclosed.isOpen_compl
  have hx' : (⟨x, hxU⟩ : U) ∈ ((Subtype.val : U → X) ⁻¹' s)ᶜ := hx
  apply Filter.mem_of_superset (hopen.mem_nhds (mem_image_of_mem _ hx'))
  rintro _ ⟨y, hy, rfl⟩
  exact hy

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
