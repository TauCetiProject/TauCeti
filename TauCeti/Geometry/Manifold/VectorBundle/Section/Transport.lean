/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Map.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Topology
import TauCeti.Geometry.Manifold.VectorBundle.Hom.Section
import TauCeti.Geometry.Manifold.VectorBundle.Section.Map.Topology
import TauCeti.Topology.VectorBundle.Trivialization

/-!
# Continuous transport on fixed-support bundle sections

Smooth fibrewise linear maps act continuously on the compact derivative topology of sections
and on every fixed-support stage. Applied to a smooth bundle isomorphism and its inverse, these
results give the fixed-support continuity comparisons needed when transporting test sections
through a smooth identification of their underlying bundles. No inductive-limit assertion is
made here.

In local frames the operator is multiplication by the smooth Hom-bundle coefficient. This works
for arbitrary model fibres given a smooth Hom-bundle section. Over a complete field with finite
source rank, smoothness of the total-space map suffices instead.

For shared frame domains there is no covering or local compactness requirement. For independent
systems over a locally compact base model, `continuous_map_frameTopology` supplies unrestricted
continuity with a covering source system, and `continuous_mapSupportedIn_of_cover` restricts
it to any fixed-support stage.
-/

public noncomputable section

open Bundle Set TopologicalSpace
open scoped ContDiff Manifold

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
    (fun p : TotalSpace F V ↦ (⟨p.proj, ϕ p.proj p.snd⟩ : TotalSpace G W)))

omit [ContMDiffVectorBundle n F V I] [ContMDiffVectorBundle n G W I] [IsManifold I n M] in
private theorem continuous_mapSupportedIn_of_continuous
    [TopologicalSpace Cₛ^n⟮I; F, V⟯] [TopologicalSpace Cₛ^n⟮I; G, W⟯]
    (h : Continuous (mapLinearMap ϕ hϕ)) (K : Set M) :
    Continuous (mapSupportedIn ϕ hϕ K) := by
  apply continuous_induced_rng.2
  simpa only [Function.comp_def, coe_mapSupportedIn] using
    (h.comp (continuous_subtypeVal : Continuous (Subtype.val : supportedIn I F n V K → _)))

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
    _ = ((e.continuousLinearMap (RingHom.id 𝕜) f) ⟨(x : M), A x⟩).snd
        (e ⟨(x : M), s x⟩).snd :=
      congrArg₂ (fun (L : F →L[𝕜] G) (v : F) ↦ L v)
        (Bundle.Trivialization.frameCoordinates_apply
          (e.continuousLinearMap (RingHom.id 𝕜) f) (fun x hx ↦ ⟨hU hx, hU' hx⟩) A x)
        (Bundle.Trivialization.frameCoordinates_apply e hU s x)
    _ = (f ⟨(x : M), A x (s x)⟩).snd := by
      rw [Bundle.Trivialization.continuousLinearMap_apply]
      simp only [ContinuousLinearMap.comp_apply]
      rw [e.symmL_apply (hU x.property), e.symm_apply_apply_mk (hU x.property),
        f.continuousLinearMapAt_apply_of_mem 𝕜 (hU' x.property)]

variable {ι : Type*} (e : ι → Trivialization F (π F V))
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
      ((A.contMDiff.comp (contMDiff_proj V)).clm_bundle_apply contMDiff_id)) :=
  continuous_frameTopology_of_frameCoordinates_eq_clmApplyLinearMap e U hU f hU'
    (fun i ↦ ((e i).continuousLinearMap (RingHom.id 𝕜) (f i)).frameCoordinates
      (fun _ hx ↦ ⟨hU i hx, hU' i hx⟩) A)
    (fun i ↦ frameCoordinates_mapLinearMap A (e i) (f i) (hU i) (hU' i))

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

end HomSection

/-- Smooth fibrewise linear transport is continuous on every fixed-support stage for an
independent target frame system, provided the source domains cover and the base model is
locally compact. Neither fibre needs finite rank. -/
theorem continuous_mapSupportedIn_of_cover [LocallyCompactSpace E] {ι κ : Type*}
    (e : ι → Trivialization F (π F V)) [∀ i, MemTrivializationAtlas (e i)]
    (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)
    (hcover : ∀ x : M, ∃ i, x ∈ U i)
    (f : κ → Trivialization G (π G W)) [∀ j, MemTrivializationAtlas (f j)]
    (U' : κ → Opens M) (hU' : ∀ j, (U' j : Set M) ⊆ (f j).baseSet) (K : Set M) :
    letI := frameTopology (I := I) (n := n) e U hU
    letI := frameTopology (I := I) (n := n) f U' hU'
    Continuous (mapSupportedIn ϕ hϕ K) := by
  let := frameTopology (I := I) (n := n) e U hU
  let := frameTopology (I := I) (n := n) f U' hU'
  apply continuous_mapSupportedIn_of_continuous
  rw [coe_mapLinearMap]
  exact continuous_map_frameTopology (fun x ↦ ϕ x) hϕ e U hU f U' hU' hcover

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]

variable {ι : Type*} (e : ι → Trivialization F (π F V))
  [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)
  (f : ι → Trivialization G (π G W)) [∀ i, MemTrivializationAtlas (f i)]
  (hU' : ∀ i, (U i : Set M) ⊆ (f i).baseSet)

/-- For finite source rank over a complete field, total-space smoothness suffices for
continuity on the compact derivative section topologies for a common system of open domains.
If the domains cover and `E` is locally compact, these topologies are frame-independent. -/
theorem continuous_mapLinearMap_frameTopology :
    letI := frameTopology (I := I) (n := n) e U hU
    letI := frameTopology (I := I) (n := n) f U hU'
    Continuous (mapLinearMap ϕ hϕ) := by
  let := frameTopology (I := I) (n := n) e U hU
  let := frameTopology (I := I) (n := n) f U hU'
  let := VectorBundle.isTopologicalAddGroup 𝕜 G W
  let := VectorBundle.continuousSMul 𝕜 G W
  refine (continuous_mapLinearMap_frameTopology_of_homSection
    (TauCeti.homSectionOfTotalSpaceMap ϕ hϕ) e U hU f hU').congr fun s ↦ ?_
  ext x
  simp only [mapLinearMap_apply, TauCeti.homSectionOfTotalSpaceMap_apply]

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

end ContMDiffSection
