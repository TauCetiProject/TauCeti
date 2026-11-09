/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.Spectral.ConstructibleTopology
public import Mathlib.Topology.Spectral.Prespectral
import Mathlib.Topology.WithTopology

/-!
# Maps, generic points and separation for the constructible topology

The constructible topology refines the given topology on a prespectral space. Spectral maps
are continuous for the constructible topologies, and every generic point of the closure of a
subset lies in its constructible closure. These facts let pro-constructible subspaces inherit
compactness and quasi-sobriety under their respective ambient hypotheses. On a T₀ prespectral
space the constructible topology is totally separated, which makes compact subsets of it closed.

## Main results

* `IsOpen.isOpen_constructibleTopology`: an open subset of a prespectral space is open for
  the constructible topology.
* `TauCeti.continuous_ofTopology_withConstructibleTopology`: the map from the constructible
  topology to the given topology of a prespectral space is continuous.
* `IsSpectralMap.continuous_constructibleTopology`: a spectral map is continuous for the
  constructible topologies; `IsSpectralMap.continuous_withConstructibleTopology` is the same
  statement for the induced map between the `WithConstructibleTopology` type synonyms.
* `IsGenericPoint.mem_closure_constructibleTopology`: a generic point of the closure of a
  subset lies in its constructible closure, in any topological space.
* `PrespectralSpace.exists_isOpen_isCompact_of_not_specializes`: if `x` does not specialize to
  `y`, a quasi-compact open subset contains `y` but not `x`.
* `IsCompact.eq_sInter_of_stableUnderGeneralization`: in a prespectral space, a quasi-compact
  subset stable under generalization is the intersection of the quasi-compact opens containing it.
* `IsCompact.isClopen_preimage_ofTopology_of_isOpen`: a quasi-compact open subset is clopen
  in `WithConstructibleTopology X`.
* `WithConstructibleTopology.instTotallySeparatedSpace`: the constructible topology of a T₀
  prespectral space is totally separated, hence Hausdorff and totally disconnected. On a spectral
  space it is also compact (`compactSpace_withConstructibleTopology`), so it is profinite.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, §3.
* P. Scholze, *Étale cohomology of diamonds*, arXiv:1709.07343, §2 (the paragraph after
  Theorem 2.2).
-/

public section

open Set Topology TopologicalSpace

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-! ### The constructible topology refines the given topology -/

/-- On a prespectral space every open subset is open for the constructible topology: an open set
is a union of quasi-compact opens, and those belong to the defining subbasis. -/
theorem IsOpen.isOpen_constructibleTopology [PrespectralSpace X] {s : Set X} (hs : IsOpen s) :
    IsOpen[constructibleTopology X] s := by
  rw [(PrespectralSpace.isTopologicalBasis (X := X)).open_eq_sUnion' hs]
  refine @isOpen_sUnion X (constructibleTopology X) _ ?_
  rintro U ⟨⟨hUo, hUc⟩, -⟩
  exact hUc.isOpen_constructibleTopology_of_isOpen hUo

variable (X) in
/-- On a prespectral space the identity map from the constructible topology to the given topology
is continuous. -/
theorem TauCeti.continuous_ofTopology_withConstructibleTopology [PrespectralSpace X] :
    Continuous (WithTopology.ofTopology : WithConstructibleTopology X → X) :=
  continuous_def.2 fun _ hs ↦
    WithConstructibleTopology.isOpen_iff.2 hs.isOpen_constructibleTopology

/-- A spectral map is continuous for the constructible topologies: it pulls the defining subbasis
back into itself. -/
theorem IsSpectralMap.continuous_constructibleTopology {f : X → Y} (hf : IsSpectralMap f) :
    Continuous[constructibleTopology X, constructibleTopology Y] f := by
  refine continuous_generateFrom_iff.2 fun U hU ↦ ?_
  obtain ⟨hUo, hUc⟩ | ⟨hUcl, hUcc⟩ := hU
  · exact (hUc.preimage_of_isOpen hf hUo).isOpen_constructibleTopology_of_isOpen
      (hUo.preimage hf.continuous)
  · refine IsCompact.isOpen_constructibleTopology_of_isClosed ?_ (hUcl.preimage hf.continuous)
    rw [← Set.preimage_compl]
    exact hUcc.preimage_of_isOpen hf hUcl.isOpen_compl

/-- A spectral map induces a continuous map between the `WithConstructibleTopology` type
synonyms. -/
theorem IsSpectralMap.continuous_withConstructibleTopology {f : X → Y} (hf : IsSpectralMap f) :
    Continuous (WithTopology.toTopology (constructibleTopology Y) ∘ f ∘ WithTopology.ofTopology :
      WithConstructibleTopology X → WithConstructibleTopology Y) :=
  @Continuous.comp _ Y _ _ (constructibleTopology Y) _ _ _
    (WithTopology.continuous_toTopology _) <|
    @Continuous.comp _ X Y _ (constructibleTopology X) (constructibleTopology Y) _ _
      hf.continuous_constructibleTopology (WithTopology.continuous_ofTopology _)

/-- Every generic point of the closure of a subset lies in its closure for the constructible
topology. -/
theorem IsGenericPoint.mem_closure_constructibleTopology {s : Set X} {η : X}
    (hη : IsGenericPoint η (closure s)) : η ∈ closure[constructibleTopology X] s := by
  -- A constructible basic neighborhood is a finite intersection of subbasic sets. The closed
  -- factors contain all of `closure s`; the intersection of the open factors must meet `s`.
  have hb := @isTopologicalBasis_of_subbasis X (constructibleTopology X)
    (constructibleTopologySubbasis X) rfl
  refine (@IsTopologicalBasis.mem_closure_iff X (constructibleTopology X) _ hb s η).2 ?_
  rintro _ ⟨F, ⟨hFfin, hFsub⟩, rfl⟩ hηF
  let O := {U ∈ F | IsOpen U}
  have hOfin : O.Finite := hFfin.subset fun _ hU ↦ hU.1
  have hOopen : IsOpen (⋂₀ O) := hOfin.isOpen_sInter fun _ hU ↦ hU.2
  have hηO : η ∈ ⋂₀ O := mem_sInter.2 fun U hU ↦ mem_sInter.1 hηF U hU.1
  obtain ⟨x, hxO, hxs⟩ := mem_closure_iff.1 hη.mem _ hOopen hηO
  refine ⟨x, mem_sInter.2 fun U hUF ↦ ?_, hxs⟩
  obtain ⟨hUopen, _⟩ | ⟨hUclosed, _⟩ := hFsub hUF
  · exact mem_sInter.1 hxO U ⟨hUF, hUopen⟩
  · exact (hη.mem_closed_set_iff hUclosed).1 (mem_sInter.1 hηF U hUF)
      (subset_closure hxs)

/-! ### Separation of the constructible topology -/

/-- In a prespectral space, if `x` does not specialize to `y`, then some quasi-compact open subset
contains `y` but not `x`. -/
theorem PrespectralSpace.exists_isOpen_isCompact_of_not_specializes [PrespectralSpace X]
    {x y : X} (h : ¬ x ⤳ y) : ∃ U : Set X, IsOpen U ∧ IsCompact U ∧ y ∈ U ∧ x ∉ U := by
  rw [PrespectralSpace.isTopologicalBasis.nhds_hasBasis.specializes_iff] at h
  push Not at h
  obtain ⟨U, ⟨⟨hUo, hUc⟩, hyU⟩, hxU⟩ := h
  exact ⟨U, hUo, hUc, hyU, hxU⟩

/-- In a prespectral space, a quasi-compact subset that is stable under generalization is the
intersection of the quasi-compact open subsets containing it. -/
theorem IsCompact.eq_sInter_of_stableUnderGeneralization [PrespectralSpace X] {s : Set X}
    (hs : IsCompact s) (hg : StableUnderGeneralization s) :
    s = ⋂₀ {U | IsOpen U ∧ IsCompact U ∧ s ⊆ U} := by
  refine Set.Subset.antisymm (fun x hx ↦ Set.mem_sInter.2 fun U hU ↦ hU.2.2 hx) fun x hx ↦ ?_
  by_contra hxs
  -- Each `z ∈ s` has a quasi-compact open neighbourhood `U z` missing `x`, since `x` is not a
  -- generalization of `z`.
  have hU (z : X) (hz : z ∈ s) : ∃ U : Set X, IsOpen U ∧ IsCompact U ∧ z ∈ U ∧ x ∉ U :=
    PrespectralSpace.exists_isOpen_isCompact_of_not_specializes fun h ↦ hxs (hg h hz)
  choose! U hUo hUc hzU hxU using hU
  -- Finitely many of the `U z` cover `s`; their union is a quasi-compact open missing `x`.
  obtain ⟨t, hts, htfin, hcover⟩ := hs.elim_finite_subcover_image
    (fun z hz ↦ hUo z hz) (fun w hw ↦ Set.mem_biUnion hw (hzU _ hw))
  obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.1 <| Set.mem_sInter.1 hx (⋃ z ∈ t, U z)
    ⟨isOpen_biUnion fun z hz ↦ hUo z (hts hz),
      htfin.isCompact_biUnion fun z hz ↦ hUc z (hts hz), hcover⟩
  exact hxU z (hts hz) hxz

/-- The preimage in `WithConstructibleTopology X` of a quasi-compact open subset of `X` is
clopen. -/
theorem IsCompact.isClopen_preimage_ofTopology_of_isOpen {s : Set X} (hs : IsCompact s)
    (ho : IsOpen s) :
    IsClopen (WithTopology.ofTopology ⁻¹' s : Set (WithConstructibleTopology X)) :=
  @IsClopen.preimage _ _ _ (constructibleTopology X) _
    (hs.isClopen_constructibleTopology_of_isOpen ho) _ (WithTopology.continuous_ofTopology _)

/-- The constructible topology of a T₀ prespectral space is totally separated. Hence it is
Hausdorff (`TotallySeparatedSpace.t2Space`) and totally disconnected; on a spectral space it is
moreover compact (`compactSpace_withConstructibleTopology`), that is, profinite. -/
instance WithConstructibleTopology.instTotallySeparatedSpace [PrespectralSpace X] [T0Space X] :
    TotallySeparatedSpace (WithConstructibleTopology X) := by
  -- Distinct points are separated by a quasi-compact open subset, which is clopen for the
  -- constructible topology.
  refine totallySeparatedSpace_iff_exists_isClopen.2 fun x y hxy ↦ ?_
  obtain ⟨U, hUo, ⟨hx, hy⟩ | ⟨hy, hx⟩⟩ :=
    exists_isOpen_xor_mem ((WithTopology.ofTopology_injective _).ne hxy)
  · obtain ⟨V, hVo, hVc, hxV, hyV⟩ :=
      PrespectralSpace.exists_isOpen_isCompact_of_not_specializes (hUo.not_specializes hy hx)
    exact ⟨_, hVc.isClopen_preimage_ofTopology_of_isOpen hVo, hxV, hyV⟩
  · obtain ⟨V, hVo, hVc, hyV, hxV⟩ :=
      PrespectralSpace.exists_isOpen_isCompact_of_not_specializes (hUo.not_specializes hx hy)
    exact ⟨_, (hVc.isClopen_preimage_ofTopology_of_isOpen hVo).compl, hxV, fun h ↦ h hyV⟩
