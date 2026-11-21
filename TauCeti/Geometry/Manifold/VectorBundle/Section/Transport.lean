/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Map
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Topology
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorBundle.Section.FrameCover
import TauCeti.Topology.VectorBundle.Trivialization

/-!
# Continuous transport on fixed-support bundle sections

Smooth fibrewise linear maps act continuously on the compact derivative topology of sections
and on every fixed-support stage. Applied to a smooth bundle isomorphism and its inverse, these
results give the fixed-support continuity comparisons needed when transporting test sections
through a smooth identification of their underlying bundles. No inductive-limit assertion is
made here.

In local frames the operator is multiplication by the smooth Hom-bundle coefficient. The weak
Whitney multiplication theorem controls the derivatives of this coefficient. This works for
arbitrary model fibres given a smooth Hom-bundle section. Over a complete field with finite
source rank, smoothness of the total-space map suffices instead.

The frame systems may use common domains or, when the base model space `E` is locally compact,
independent covering domains. In the latter case `ContMDiffSection.frameTopology_eq_of_covers`
identifies the topologies for different choices of cover on each bundle.
-/

public noncomputable section

open Bundle Set TopologicalSpace
open scoped ContDiff Manifold TauCeti.ManifoldWeakWhitney

namespace ContMDiffSection

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  {F G : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {V W : M → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  [∀ x, AddCommGroup (W x)] [∀ x, Module 𝕜 (W x)] [∀ x, TopologicalSpace (W x)]
  [TopologicalSpace (TotalSpace G W)] [FiberBundle G W] [VectorBundle 𝕜 G W]
  {n : ℕ∞ω} [ContMDiffVectorBundle n F V I] [ContMDiffVectorBundle n G W I]
  [IsManifold I n M]

variable (ϕ : ∀ x, V x →ₗ[𝕜] W x)
  (hϕ : ContMDiff (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, G)) n
    (fun p : TotalSpace F V ↦ (⟨p.proj, ϕ p.proj p.2⟩ : TotalSpace G W)))

omit [ContMDiffVectorBundle n F V I] [ContMDiffVectorBundle n G W I] [IsManifold I n M] in
private theorem continuous_mapSupportedIn_of_continuous
    [TopologicalSpace Cₛ^n⟮I; F, V⟯] [TopologicalSpace Cₛ^n⟮I; G, W⟯]
    (h : Continuous (mapLinearMap ϕ hϕ)) (K : Set M) :
    Continuous (mapSupportedIn ϕ hϕ K) := by
  apply continuous_induced_rng.2
  simpa only [Function.comp_def, coe_mapSupportedIn] using
    (h.comp (continuous_subtype_val : Continuous (Subtype.val : supportedIn I F n V K → _)))

section HomSection

variable [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul 𝕜 (W x)]
  (A : Cₛ^n⟮I; F →L[𝕜] G, fun x ↦ V x →L[𝕜] W x⟯)

omit [IsManifold I n M] in
/-- In frames over a common open set, transport by a smooth Hom-bundle section is pointwise
multiplication by its smooth coefficient. -/
theorem frameCoordinates_mapLinearMap
    (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
    (f : Trivialization G (π G W)) [MemTrivializationAtlas f]
    {U : Opens M} (hU : (U : Set M) ⊆ e.baseSet) (hU' : (U : Set M) ⊆ f.baseSet)
    (s : Cₛ^n⟮I; F, V⟯) :
    f.frameCoordinates hU' (mapLinearMap (fun x ↦ (A x).toLinearMap)
      ((A.contMDiff.comp (contMDiff_proj V)).clm_bundle_apply contMDiff_id) s) =
      ContMDiffMap.clmApplyLinearMap
        ((e.continuousLinearMap (RingHom.id 𝕜) f).frameCoordinates
          (fun x hx ↦ ⟨hU hx, hU' hx⟩) A)
        (e.frameCoordinates hU s) := by
  ext x
  rw [ContMDiffMap.clmApplyLinearMap_apply, Bundle.Trivialization.frameCoordinates_apply,
    mapLinearMap_apply]
  symm
  calc
    _ = ((e.continuousLinearMap (RingHom.id 𝕜) f) ⟨(x : M), A x⟩).2
        (e ⟨(x : M), s x⟩).2 :=
      congrArg₂ (fun (L : F →L[𝕜] G) (v : F) ↦ L v)
        (Bundle.Trivialization.frameCoordinates_apply
          (e.continuousLinearMap (RingHom.id 𝕜) f) (fun x hx ↦ ⟨hU hx, hU' hx⟩) A x)
        (Bundle.Trivialization.frameCoordinates_apply e hU s x)
    _ = (f ⟨(x : M), A x (s x)⟩).2 := by
      rw [Bundle.Trivialization.continuousLinearMap_apply]
      simp only [ContinuousLinearMap.comp_apply]
      rw [e.symmL_apply (hU x.2), e.symm_apply_apply_mk (hU x.2),
        f.continuousLinearMapAt_apply_of_mem 𝕜 (hU' x.2)]

variable {ι κ : Type*} (e : ι → Trivialization F (π F V))
  [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)

/-- A smooth Hom-bundle section acts continuously when both frame systems have the same
open domains. No covering or finite-rank hypothesis is needed. -/
theorem continuous_mapLinearMap_frameTopology_of_homSection
    (f : ι → Trivialization G (π G W)) [∀ i, MemTrivializationAtlas (f i)]
    (hU' : ∀ i, (U i : Set M) ⊆ (f i).baseSet) :
    letI := frameTopology (I := I) (n := n) e U hU
    letI := frameTopology (I := I) (n := n) f U hU'
    Continuous (mapLinearMap (fun x ↦ (A x).toLinearMap)
      ((A.contMDiff.comp (contMDiff_proj V)).clm_bundle_apply contMDiff_id)) := by
  let := frameTopology (I := I) (n := n) e U hU
  let := frameTopology (I := I) (n := n) f U hU'
  apply (continuous_frameTopology_iff_frameCoordinates f U hU').2
  intro i
  have h := (ContMDiffMap.continuous_clmApplyLinearMap
    (((e i).continuousLinearMap (RingHom.id 𝕜) (f i)).frameCoordinates
      (fun x hx ↦ ⟨hU i hx, hU' i hx⟩) A)).comp
    (continuous_frameCoordinates e U hU i)
  exact h.congr fun s ↦ (frameCoordinates_mapLinearMap A (e i) (f i) (hU i) (hU' i) s).symm

/-- A smooth Hom-bundle section acts continuously for independently chosen covering frame
systems on the source and target when the base model is locally compact. -/
theorem continuous_mapLinearMap_frameTopology_of_homSection_of_covers [LocallyCompactSpace E]
    (hcover : ∀ x : M, ∃ i, x ∈ U i)
    (f : κ → Trivialization G (π G W)) [∀ j, MemTrivializationAtlas (f j)]
    (U' : κ → Opens M) (hU' : ∀ j, (U' j : Set M) ⊆ (f j).baseSet)
    (hcover' : ∀ x : M, ∃ j, x ∈ U' j) :
    letI := frameTopology (I := I) (n := n) e U hU
    letI := frameTopology (I := I) (n := n) f U' hU'
    Continuous (mapLinearMap (fun x ↦ (A x).toLinearMap)
      ((A.contMDiff.comp (contMDiff_proj V)).clm_bundle_apply contMDiff_id)) := by
  let D (p : ι × κ) := U p.1 ⊓ U' p.2
  have hD (p : ι × κ) : (D p : Set M) ⊆ (e p.1).baseSet := fun _ hx ↦ hU p.1 hx.1
  have hD' (p : ι × κ) : (D p : Set M) ⊆ (f p.2).baseSet := fun _ hx ↦ hU' p.2 hx.2
  have hDc (x : M) : ∃ p, x ∈ D p := by
    obtain ⟨i, hi⟩ := hcover x
    obtain ⟨j, hj⟩ := hcover' x
    exact ⟨(i, j), hi, hj⟩
  rw [frameTopology_eq_of_covers e U hU hcover (fun p : ι × κ ↦ e p.1) D hD hDc,
    frameTopology_eq_of_covers f U' hU' hcover' (fun p : ι × κ ↦ f p.2) D hD' hDc]
  exact continuous_mapLinearMap_frameTopology_of_homSection A _ D hD _ hD'

/-- Transport by a smooth Hom-bundle section is continuous on every fixed-support stage when
both frame systems have the same open domains. -/
theorem continuous_mapSupportedIn_of_homSection
    (f : ι → Trivialization G (π G W)) [∀ i, MemTrivializationAtlas (f i)]
    (hU' : ∀ i, (U i : Set M) ⊆ (f i).baseSet) (K : Set M) :
    letI := frameTopology (I := I) (n := n) e U hU
    letI := frameTopology (I := I) (n := n) f U hU'
    Continuous (mapSupportedIn (fun x ↦ (A x).toLinearMap)
      ((A.contMDiff.comp (contMDiff_proj V)).clm_bundle_apply contMDiff_id) K) := by
  let := frameTopology (I := I) (n := n) e U hU
  let := frameTopology (I := I) (n := n) f U hU'
  exact continuous_mapSupportedIn_of_continuous _ _
    (continuous_mapLinearMap_frameTopology_of_homSection A e U hU f hU') K

/-- Transport by a smooth Hom-bundle section is continuous on every fixed-support stage for
independent covering frame systems when the base model is locally compact. -/
theorem continuous_mapSupportedIn_of_homSection_of_covers [LocallyCompactSpace E]
    (hcover : ∀ x : M, ∃ i, x ∈ U i)
    (f : κ → Trivialization G (π G W)) [∀ j, MemTrivializationAtlas (f j)]
    (U' : κ → Opens M) (hU' : ∀ j, (U' j : Set M) ⊆ (f j).baseSet)
    (hcover' : ∀ x : M, ∃ j, x ∈ U' j) (K : Set M) :
    letI := frameTopology (I := I) (n := n) e U hU
    letI := frameTopology (I := I) (n := n) f U' hU'
    Continuous (mapSupportedIn (fun x ↦ (A x).toLinearMap)
      ((A.contMDiff.comp (contMDiff_proj V)).clm_bundle_apply contMDiff_id) K) := by
  let := frameTopology (I := I) (n := n) e U hU
  let := frameTopology (I := I) (n := n) f U' hU'
  exact continuous_mapSupportedIn_of_continuous _ _
    (continuous_mapLinearMap_frameTopology_of_homSection_of_covers A e U hU hcover f U' hU'
      hcover') K

end HomSection

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]

private def homSectionOfTotalSpaceMap
    [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul 𝕜 (W x)] :
    Cₛ^n⟮I; F →L[𝕜] G, fun x ↦ V x →L[𝕜] W x⟯ := by
  let ϕL (x : M) : V x →L[𝕜] W x :=
    { toLinearMap := ϕ x
      cont := (FiberBundle.totalSpaceMk_isInducing G W x).continuous_iff.2
        (hϕ.continuous.comp (FiberBundle.continuous_totalSpaceMk F V x)) }
  exact ⟨ϕL, (TauCeti.contMDiff_hom_bundle_iff ϕL).2 hϕ⟩

variable {ι κ : Type*} (e : ι → Trivialization F (π F V))
  [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)

section CommonDomains

variable (f : ι → Trivialization G (π G W)) [∀ i, MemTrivializationAtlas (f i)]
  (hU' : ∀ i, (U i : Set M) ⊆ (f i).baseSet)

/-- For finite source rank over a complete field, total-space smoothness suffices for
continuity on the compact derivative section topologies for a common system of open domains.
If the domains cover and `E` is locally compact, these topologies are frame-independent. -/
theorem continuous_mapLinearMap_frameTopology :
    letI := frameTopology (I := I) (n := n) e U hU
    letI := frameTopology (I := I) (n := n) f U hU'
    Continuous (mapLinearMap ϕ hϕ) := by
  let := VectorBundle.isTopologicalAddGroup 𝕜 G W
  let := VectorBundle.continuousSMul 𝕜 G W
  exact continuous_mapLinearMap_frameTopology_of_homSection (homSectionOfTotalSpaceMap ϕ hϕ)
    e U hU f hU'

/-- For finite source rank over a complete field, total-space smoothness suffices for
continuity on every fixed-support stage for a common system of open domains. -/
theorem continuous_mapSupportedIn (K : Set M) :
    letI := frameTopology (I := I) (n := n) e U hU
    letI := frameTopology (I := I) (n := n) f U hU'
    Continuous (mapSupportedIn ϕ hϕ K) := by
  let := frameTopology (I := I) (n := n) e U hU
  let := frameTopology (I := I) (n := n) f U hU'
  exact continuous_mapSupportedIn_of_continuous ϕ hϕ
    (continuous_mapLinearMap_frameTopology ϕ hϕ e U hU f hU') K

end CommonDomains

section Covers

variable [LocallyCompactSpace E] (hcover : ∀ x : M, ∃ i, x ∈ U i)
  (f : κ → Trivialization G (π G W)) [∀ j, MemTrivializationAtlas (f j)]
  (U' : κ → Opens M) (hU' : ∀ j, (U' j : Set M) ⊆ (f j).baseSet)
  (hcover' : ∀ x : M, ∃ j, x ∈ U' j)

include hcover hcover'

/-- A smooth total-space map of finite source rank over a complete field induces continuous
section transport for independent covering frame systems when the base model is locally compact. -/
theorem continuous_mapLinearMap_frameTopology_of_covers :
    letI := frameTopology (I := I) (n := n) e U hU
    letI := frameTopology (I := I) (n := n) f U' hU'
    Continuous (mapLinearMap ϕ hϕ) := by
  let := VectorBundle.isTopologicalAddGroup 𝕜 G W
  let := VectorBundle.continuousSMul 𝕜 G W
  exact continuous_mapLinearMap_frameTopology_of_homSection_of_covers
    (homSectionOfTotalSpaceMap ϕ hϕ) e U hU hcover f U' hU' hcover'

/-- A smooth total-space map of finite source rank over a complete field induces continuous
transport on every fixed-support stage for independent covering frame systems when the base
model is locally compact. -/
theorem continuous_mapSupportedIn_of_covers (K : Set M) :
    letI := frameTopology (I := I) (n := n) e U hU
    letI := frameTopology (I := I) (n := n) f U' hU'
    Continuous (mapSupportedIn ϕ hϕ K) := by
  let := frameTopology (I := I) (n := n) e U hU
  let := frameTopology (I := I) (n := n) f U' hU'
  exact continuous_mapSupportedIn_of_continuous ϕ hϕ
    (continuous_mapLinearMap_frameTopology_of_covers ϕ hϕ e U hU hcover f U' hU' hcover') K

end Covers

end ContMDiffSection
