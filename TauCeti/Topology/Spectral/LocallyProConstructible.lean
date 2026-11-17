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

Local pro-constructibility can be tested on an open cover, is preserved under pullback along
locally spectral maps into locally spectral spaces, and passes local spectrality to subspaces
together with their inclusions. On a locally spectral space, the closure of a locally
pro-constructible subset is its set of specializations; in particular, such a subset is closed
exactly when it is stable under specialization, and an open locally spectral map between locally
spectral spaces is generalizing.

A quasi-compact locally spectral map out of a locally spectral space carries locally
pro-constructible subsets to locally pro-constructible subsets. Here quasi-compactness is
expressed by Mathlib's `IsSpectralMap`: inverse images of compact opens are compact. Between
locally spectral spaces, such a map is closed exactly when it is a `SpecializingMap`. These are
the topological image and closedness criteria used in properness arguments in adic geometry.

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

/-- Pullback along an open embedding preserves local pro-constructibility. -/
theorem IsLocallyProConstructible.preimage_of_isOpenEmbedding {f : X → Y} {s : Set Y}
    (hs : IsLocallyProConstructible s) (hf : IsOpenEmbedding f) :
    IsLocallyProConstructible (f ⁻¹' s) := by
  intro U hU hUs
  have := hUs
  let g : U → Y := f ∘ Subtype.val
  have hg : IsOpenEmbedding g := hf.comp hU.isOpenEmbedding_subtypeVal
  let h := hg.isEmbedding.toHomeomorph
  have : CompactSpace (range g) := h.compactSpace
  have : SpectralSpace (range g) := h.symm.isOpenEmbedding.spectralSpace
  have htrace := hs.isProConstructible_preimage hg.isOpen_range
  convert htrace.preimage h.isOpenEmbedding.isSpectralMap using 1
  ext x
  simp [h, g]

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

/-- Local pro-constructibility can be tested on any open cover. -/
theorem IsLocallyProConstructible.of_isOpenCover {ι : Type*} {U : ι → Opens X}
    (hU : IsOpenCover U)
    (hs : ∀ i, IsLocallyProConstructible ((Subtype.val : U i → X) ⁻¹' s)) :
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
    have hW : IsProConstructible ((Subtype.val : W x → X) ⁻¹' s) := by
      convert isLocallyProConstructible_iff_isProConstructible.mp
        ((hs (i x)).preimage_of_isOpenEmbedding hg) using 1
      ext y
      simp [g]
    exact hW.image he.isSpectralMap
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
      obtain ⟨x, -, z, hz, rfl⟩ := mem_iUnion₂.mp hy
      simpa [e] using hz
  rw [heq]
  exact T.finite_toSet.isProConstructible_biUnion fun x _ ↦ himage x

/-- Local pro-constructibility is equivalent to local pro-constructibility on an open cover. -/
theorem IsLocallyProConstructible.iff_of_isOpenCover {ι : Type*} {U : ι → Opens X}
    (hU : IsOpenCover U) :
    IsLocallyProConstructible s ↔
      ∀ i, IsLocallyProConstructible ((Subtype.val : U i → X) ⁻¹' s) :=
  ⟨fun hs i ↦ hs.preimage_of_isOpenEmbedding (U i).isOpen.isOpenEmbedding_subtypeVal,
    of_isOpenCover hU⟩

/-- Pro-constructible traces on a quasiseparated open cover imply local pro-constructibility. -/
theorem IsLocallyProConstructible.of_isOpenCover_of_isProConstructible
    {ι : Type*} {U : ι → Opens X} (hU : IsOpenCover U) [∀ i, QuasiSeparatedSpace (U i)]
    (hs : ∀ i, IsProConstructible ((Subtype.val : U i → X) ⁻¹' s)) :
    IsLocallyProConstructible s :=
  .of_isOpenCover hU fun i ↦ (hs i).isLocallyProConstructible

/-- Closed subsets are locally pro-constructible, without any ambient separation hypothesis. -/
theorem _root_.IsClosed.isLocallyProConstructible (hs : IsClosed s) :
    IsLocallyProConstructible s := by
  intro U _ hUs
  have := hUs
  exact (hs.preimage continuous_subtype_val).isProConstructible

/-- The closure of a locally pro-constructible subset of a locally spectral space consists of
its specializations. -/
theorem IsLocallyProConstructible.closure_eq_setOfPred_specializes
    (hs : IsLocallyProConstructible s) (hX : IsLocallySpectralSpace X) :
    closure s = {y | ∃ x ∈ s, x ⤳ y} := by
  refine Subset.antisymm (fun y hy ↦ ?_) ?_
  · obtain ⟨U, hUo, hyU, hUs⟩ := isLocallySpectralSpace_iff.mp hX y
    have := hUs
    have hy' : (⟨y, hyU⟩ : U) ∈ closure ((Subtype.val : U → X) ⁻¹' s) := by
      rw [← hUo.isOpenEmbedding_subtypeVal.isOpenMap.preimage_closure_eq_closure_preimage
        continuous_subtype_val]
      exact hy
    rw [(hs.isProConstructible_preimage hUo).closure_eq_setOfPred_specializes] at hy'
    obtain ⟨x, hx, hxy⟩ := hy'
    exact ⟨x.1, hx, hxy.map continuous_subtype_val⟩
  · rintro y ⟨x, hx, hxy⟩
    exact closure_mono (singleton_subset_iff.mpr hx) hxy.mem_closure

/-- A locally pro-constructible subset of a locally spectral space is closed exactly when it
is stable under specialization. -/
theorem IsLocallyProConstructible.isClosed_iff_stableUnderSpecialization
    (hs : IsLocallyProConstructible s) (hX : IsLocallySpectralSpace X) :
    IsClosed s ↔ StableUnderSpecialization s := by
  refine ⟨IsClosed.stableUnderSpecialization, fun hstable ↦ ?_⟩
  rw [← closure_subset_iff_isClosed, hs.closure_eq_setOfPred_specializes hX]
  rintro y ⟨x, hx, hxy⟩
  exact hstable hxy hx

/-- A quasi-compact locally spectral map out of a locally spectral space `X` carries locally
pro-constructible subsets to locally pro-constructible subsets. Quasi-compactness is expressed by
Mathlib's `IsSpectralMap`: compact open subsets have compact inverse images. No global compactness
or quasiseparatedness of `X`, or ambient hypothesis on `Y`, is assumed. -/
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

/-- Every singleton subset is locally pro-constructible, without any ambient hypothesis. -/
theorem isLocallyProConstructible_singleton (x : X) : IsLocallyProConstructible ({x} : Set X) := by
  intro U _ hUs
  have _ : SpectralSpace U := hUs
  by_cases hx : x ∈ U
  · have heq : (Subtype.val : U → X) ⁻¹' {x} = {(⟨x, hx⟩ : U)} := by
      ext u
      simp [Subtype.ext_iff]
    rw [heq]
    exact isProConstructible_singleton (⟨x, hx⟩ : U)
  · have heq : (Subtype.val : U → X) ⁻¹' {x} = ∅ :=
      eq_empty_iff_forall_notMem.mpr fun u hu ↦ hx (hu ▸ u.2)
    rw [heq]
    exact isProConstructible_empty

/-- Locally pro-constructible subsets pull back along locally spectral maps into locally spectral
spaces. -/
theorem IsLocallyProConstructible.preimage {f : X → Y} {s : Set Y}
    (hs : IsLocallyProConstructible s) (hY : IsLocallySpectralSpace Y)
    (hf : IsLocallySpectralMap f) : IsLocallyProConstructible (f ⁻¹' s) := by
  intro U hUo hUs
  have _ : SpectralSpace U := hUs
  have hcharts (u : U) : ∃ (V : Set Y) (W : Set X), IsOpen V ∧ SpectralSpace V ∧
      W ⊆ U ∩ f ⁻¹' V ∧ IsOpen W ∧ u.1 ∈ W ∧ SpectralSpace W := by
    obtain ⟨V, hVo, hfuV, hVs⟩ := isLocallySpectralSpace_iff.mp hY (f u.1)
    obtain ⟨W, hWsub, hWo, huW, -, hWs⟩ :=
      hUo.exists_spectralSpace_subset_inter hUs (hVo.preimage hf.continuous) u.2 hfuV
    exact ⟨V, W, hVo, hVs, hWsub, hWo, huW, hWs⟩
  choose V W hVo hVs hWsub hWo huW hWs using hcharts
  let cov : U → Opens U := fun u ↦ ⟨(Subtype.val : U → X) ⁻¹' W u,
    (hWo u).preimage continuous_subtype_val⟩
  have hcov : IsOpenCover cov := IsOpenCover.of_sets (fun u ↦ (cov u).isOpen) <| by
    refine eq_univ_iff_forall.mpr fun u ↦ mem_iUnion.mpr ⟨u, huW u⟩
  let e (u : U) : cov u ≃ₜ W u :=
    { toFun := fun x ↦ ⟨x.1.1, x.2⟩
      invFun := fun x ↦ ⟨⟨x.1, (hWsub u x.2).1⟩, x.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }
  have _ : ∀ u : U, QuasiSeparatedSpace (cov u) := fun u ↦ by
    have _ : SpectralSpace (W u) := hWs u
    exact (e u).isOpenEmbedding.quasiSeparatedSpace
  refine isLocallyProConstructible_iff_isProConstructible.mp
    (.of_isOpenCover_of_isProConstructible hcov fun u ↦ ?_)
  have _ : SpectralSpace (V u) := hVs u
  have _ : SpectralSpace (W u) := hWs u
  have _ : CompactSpace (cov u) := (e u).symm.compactSpace
  have hWV : MapsTo f (W u) (V u) := fun x hx ↦ (hWsub u hx).2
  have htrace : IsProConstructible ((Subtype.val : V u → Y) ⁻¹' s) :=
    hs.isProConstructible_preimage (hVo u)
  have hWtrace := htrace.preimage (hf.isSpectralMap_restrict hWV (hWo u) (hVo u))
  exact hWtrace.preimage (e u).isOpenEmbedding.isSpectralMap

private lemma IsLocallyProConstructible.spectralSpace_and_isSpectralMap_preimage
    (hs : IsLocallyProConstructible s) {U : Set X} (hUo : IsOpen U) [SpectralSpace U] :
    SpectralSpace ((Subtype.val : s → X) ⁻¹' U : Set s) ∧
      IsSpectralMap ((mapsTo_preimage (Subtype.val : s → X) U).restrict Subtype.val
        ((Subtype.val : s → X) ⁻¹' U) U) := by
  let e : ((Subtype.val : s → X) ⁻¹' U : Set s) ≃ₜ
      ((Subtype.val : U → X) ⁻¹' s : Set U) :=
    { toFun := fun x ↦ ⟨⟨x.1.1, x.2⟩, x.1.2⟩
      invFun := fun x ↦ ⟨⟨x.1.1, x.2⟩, x.1.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun :=
        ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _
      continuous_invFun :=
        ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _ }
  have _ : SpectralSpace ((Subtype.val : U → X) ⁻¹' s : Set U) :=
    (hs.isProConstructible_preimage hUo).spectralSpace
  have _ : CompactSpace ((Subtype.val : s → X) ⁻¹' U : Set s) := e.symm.compactSpace
  refine ⟨e.isOpenEmbedding.spectralSpace, ?_⟩
  have hcomp :
      (mapsTo_preimage (Subtype.val : s → X) U).restrict Subtype.val _ U =
        Subtype.val ∘ e := rfl
  rw [hcomp]
  exact (hs.isProConstructible_preimage hUo).isSpectralMap_subtypeVal.comp
    e.isOpenEmbedding.isSpectralMap

/-- A locally pro-constructible subspace of a locally spectral space is locally spectral. -/
theorem IsLocallyProConstructible.isLocallySpectralSpace (hs : IsLocallyProConstructible s)
    (hX : IsLocallySpectralSpace X) : IsLocallySpectralSpace s := by
  refine isLocallySpectralSpace_iff.mpr fun ⟨x, hx⟩ ↦ ?_
  obtain ⟨U, hUo, hxU, hUs⟩ := isLocallySpectralSpace_iff.mp hX x
  have _ : SpectralSpace U := hUs
  exact ⟨(Subtype.val : s → X) ⁻¹' U, hUo.preimage continuous_subtype_val, hxU,
    (hs.spectralSpace_and_isSpectralMap_preimage hUo).1⟩

/-- The inclusion of a locally pro-constructible subset of a locally spectral space is locally
spectral. -/
theorem IsLocallyProConstructible.isLocallySpectralMap_subtypeVal
    (hs : IsLocallyProConstructible s) (hX : IsLocallySpectralSpace X) :
    IsLocallySpectralMap ((↑) : s → X) := by
  refine .of_forall_exists fun ⟨x, hx⟩ ↦ ?_
  obtain ⟨U, hUo, hxU, hUs⟩ := isLocallySpectralSpace_iff.mp hX x
  have _ : SpectralSpace U := hUs
  obtain ⟨hWs, hspec⟩ := hs.spectralSpace_and_isSpectralMap_preimage hUo
  exact ⟨(Subtype.val : s → X) ⁻¹' U, U, mapsTo_preimage Subtype.val U,
    hUo.preimage continuous_subtype_val, hUo, hxU, hWs.toQuasiSeparatedSpace, hspec⟩

/-- An open locally spectral map between locally spectral spaces is generalizing. -/
theorem IsLocallySpectralMap.generalizingMap_of_isOpenMap {f : X → Y}
    (hf : IsLocallySpectralMap f) (hX : IsLocallySpectralSpace X)
    (hY : IsLocallySpectralSpace Y) (ho : IsOpenMap f) : GeneralizingMap f := by
  intro x y hy
  have hfib : IsLocallyProConstructible (f ⁻¹' {y}) :=
    (isLocallyProConstructible_singleton y).preimage hY hf
  have hxcl : x ∈ closure (f ⁻¹' {y}) := mem_closure_iff.mpr fun U hUo hxU ↦ by
    obtain ⟨x', hx'U, hx'y⟩ := hy.mem_open (ho U hUo) ⟨x, hxU, rfl⟩
    exact ⟨x', hx'U, hx'y⟩
  rw [hfib.closure_eq_setOfPred_specializes hX] at hxcl
  obtain ⟨x', hx'y, hx'x⟩ := hxcl
  exact ⟨x', hx'x, hx'y⟩

end TauCeti
