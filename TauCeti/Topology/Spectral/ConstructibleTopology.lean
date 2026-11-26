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
compactness and quasi-sobriety under their respective ambient hypotheses. On a spectral space the
constructible subsets are exactly the clopens of the constructible topology, and they form a
basis of it. On a T₀ prespectral space the constructible topology is totally separated, which
makes compact subsets of it closed.

## Main results

* `IsOpen.isOpen_constructibleTopology`: an open subset of a prespectral space is open for
  the constructible topology.
* `TauCeti.continuous_ofTopology_withConstructibleTopology`: the map from the constructible
  topology to the given topology of a prespectral space is continuous.
* `TauCeti.compactSpace_constructibleTopology`: on a compact, quasi-sober, quasi-separated
  prespectral space the constructible topology is compact.
* `IsSpectralMap.continuous_constructibleTopology`: a spectral map is continuous for the
  constructible topologies; `IsSpectralMap.continuous_withConstructibleTopology` is the same
  statement for the induced map between the `WithConstructibleTopology` type synonyms.
* `IsGenericPoint.mem_closure_constructibleTopology`: a generic point of the closure of a
  subset lies in its constructible closure, in any topological space.
* `TauCeti.isTopologicalBasis_constructibleTopology`: on a compact quasi-separated space the
  constructible subsets form a basis of the constructible topology.
* `TauCeti.isClopen_constructibleTopology_iff_isConstructible`: on a spectral space the clopen
  subsets of the constructible topology are exactly the constructible subsets.
* `PrespectralSpace.not_specializes_iff_exists_isOpen_isCompact`: `x` does not specialize to `y`
  if and only if some quasi-compact open subset contains `y` but not `x`.
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

variable (X) in
/-- On a compact, quasi-sober, quasi-separated prespectral space (for instance a spectral space) the
constructible topology is compact. This is Mathlib's `compactSpace_withConstructibleTopology` for
the topology itself rather than for the type synonym `WithConstructibleTopology X`. -/
theorem TauCeti.compactSpace_constructibleTopology [CompactSpace X] [QuasiSober X]
    [PrespectralSpace X] [QuasiSeparatedSpace X] : @CompactSpace X (constructibleTopology X) :=
  @Function.Surjective.compactSpace _ _ _ (constructibleTopology X) _
    (WithTopology.continuous_ofTopology _) _ (WithTopology.ofTopology_surjective _)

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

/-! ### Constructible subsets as clopens of the constructible topology -/

variable (X) in
/-- On a compact quasi-separated space the constructible subsets form a basis of the
constructible topology: they generate it and are stable under finite intersections. -/
theorem TauCeti.isTopologicalBasis_constructibleTopology [CompactSpace X]
    [QuasiSeparatedSpace X] :
    @IsTopologicalBasis X (constructibleTopology X) {s : Set X | IsConstructible s} :=
  @isTopologicalBasis_of_subbasis_of_finiteInter X (constructibleTopology X) _
    (constructibleTopology_eq_generateFrom_isConstructible X)
    ⟨IsConstructible.univ, fun _ hs _ ht ↦ hs.inter ht⟩

/-- On a compact quasi-separated space a constructible subset is clopen for the constructible
topology. -/
theorem Topology.IsConstructible.isClopen_constructibleTopology [CompactSpace X]
    [QuasiSeparatedSpace X] {s : Set X} (hs : IsConstructible s) :
    IsClopen[constructibleTopology X] s := by
  have hb := TauCeti.isTopologicalBasis_constructibleTopology X
  exact ⟨@IsClosed.mk X (constructibleTopology X) s
      (@IsTopologicalBasis.isOpen X (constructibleTopology X) _ _ hb hs.compl),
    @IsTopologicalBasis.isOpen X (constructibleTopology X) _ _ hb hs⟩

/-- On a compact, quasi-sober, quasi-separated prespectral space (for instance a spectral space)
the subsets that are clopen for the constructible topology are exactly the constructible subsets.
A clopen subset is compact for the compact constructible topology, hence a finite union of basic
constructible subsets. -/
theorem TauCeti.isClopen_constructibleTopology_iff_isConstructible [CompactSpace X]
    [QuasiSober X] [PrespectralSpace X] [QuasiSeparatedSpace X] {s : Set X} :
    IsClopen[constructibleTopology X] s ↔ IsConstructible s := by
  refine ⟨fun hs ↦ ?_, IsConstructible.isClopen_constructibleTopology⟩
  have hb : @IsTopologicalBasis X (constructibleTopology X)
      (range (Subtype.val : {s : Set X // IsConstructible s} → Set X)) := by
    simpa using TauCeti.isTopologicalBasis_constructibleTopology X
  have := TauCeti.compactSpace_constructibleTopology X
  obtain ⟨t, ht, rfl⟩ := @eq_finite_iUnion_of_isTopologicalBasis_of_isCompact_open X _
    (constructibleTopology X) Subtype.val hb s
    (@IsClosed.isCompact X (constructibleTopology X) s this hs.1) hs.2
  exact IsConstructible.biUnion ht fun i _ ↦ i.property

/-! ### Separation of the constructible topology -/

/-- In a prespectral space, `x` does not specialize to `y` if and only if some quasi-compact open
subset contains `y` but not `x`. -/
theorem PrespectralSpace.not_specializes_iff_exists_isOpen_isCompact [PrespectralSpace X]
    {x y : X} : ¬ x ⤳ y ↔ ∃ U : Set X, IsOpen U ∧ IsCompact U ∧ y ∈ U ∧ x ∉ U := by
  simp [PrespectralSpace.isTopologicalBasis.nhds_hasBasis.specializes_iff, and_assoc]

/-- In a prespectral space, a quasi-compact subset that is stable under generalization is the
intersection of the quasi-compact open subsets containing it. -/
theorem IsCompact.eq_sInter_of_stableUnderGeneralization [PrespectralSpace X] {s : Set X}
    (hs : IsCompact s) (hg : StableUnderGeneralization s) :
    s = ⋂₀ {U | IsOpen U ∧ IsCompact U ∧ s ⊆ U} := by
  refine Set.Subset.antisymm (subset_sInter fun _ hU ↦ hU.2.2) fun x hx ↦ ?_
  by_contra hxs
  -- Since `x ∉ s` and `s` is stable under generalization, `s` misses the closure of `{x}`. A
  -- quasi-compact open subset between `s` and the complement of that closure misses `x`.
  obtain ⟨U, hUc, hUo, hsU, hUx⟩ := PrespectralSpace.exists_isCompact_and_isOpen_between hs
    isClosed_closure.isOpen_compl fun z hz hzx ↦ hxs (hg (specializes_iff_mem_closure.2 hzx) hz)
  exact hUx (mem_sInter.1 hx U ⟨hUo, hUc, hsU⟩) (subset_closure rfl)

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
      PrespectralSpace.not_specializes_iff_exists_isOpen_isCompact.1 (hUo.not_specializes hy hx)
    exact ⟨_, hVc.isClopen_preimage_ofTopology_of_isOpen hVo, hxV, hyV⟩
  · obtain ⟨V, hVo, hVc, hyV, hxV⟩ :=
      PrespectralSpace.not_specializes_iff_exists_isOpen_isCompact.1 (hUo.not_specializes hx hy)
    exact ⟨_, (hVc.isClopen_preimage_ofTopology_of_isOpen hVo).compl, hxV, fun h ↦ h hyV⟩
