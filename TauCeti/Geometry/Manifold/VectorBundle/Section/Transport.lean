/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Map
public import TauCeti.Geometry.Manifold.VectorBundle.Section.FrameCover
public import TauCeti.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Topology.VectorBundle.Trivialization

/-!
# Continuous transport on fixed-support bundle sections

Smooth fibrewise linear maps act continuously on the compact derivative topology of sections
and on every fixed-support stage. Applied to a smooth bundle isomorphism and its inverse, these
results give the fixed-support continuity comparisons needed when transporting test sections
through a smooth identification of their underlying bundles. No inductive-limit assertion is
made here.

The source model fibre is finite dimensional; the target need not be. In local frames the
operator is multiplication by the smooth matrix of the bundle map. Continuity uses the native
weak Whitney multiplication theorem, including the derivatives of that matrix. The two frame
systems use common open domains; for covering systems the section topologies are independent
of the chosen frames by `frameTopology_eq_of_covers`.
-/

public noncomputable section

open Bundle Set TopologicalSpace
open scoped ContDiff Manifold TauCeti.ManifoldWeakWhitney

namespace ContMDiffSection

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {V W : M → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [TopologicalSpace (TotalSpace G W)] [FiberBundle G W] [VectorBundle ℝ G W]
  {n : ℕ∞ω} [ContMDiffVectorBundle n F V I] [ContMDiffVectorBundle n G W I]
  [IsManifold I n M]

variable (ϕ : ∀ x, V x →L[ℝ] W x)
  (hϕ : ContMDiff (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, G)) n
    (fun p : TotalSpace F V ↦ (⟨p.proj, ϕ p.proj p.2⟩ : TotalSpace G W)))

omit [IsManifold I n M] in
/-- In a pair of frames over the same open set, section transport is multiplication by the
smooth Hom-bundle coefficient of the bundle map. -/
theorem frameCoordinates_mapLinearMap
    (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
    (f : Trivialization G (π G W)) [MemTrivializationAtlas f]
    {U : Opens M} (hU : (U : Set M) ⊆ e.baseSet) (hU' : (U : Set M) ⊆ f.baseSet)
    (s : Cₛ^n⟮I; F, V⟯) :
    letI := VectorBundle.isTopologicalAddGroup ℝ G W
    letI := VectorBundle.continuousSMul ℝ G W
    f.frameCoordinates hU' (mapLinearMap (fun x ↦ (ϕ x).toLinearMap) hϕ s) =
      ContMDiffMap.clmApplyLinearMap
        ((e.continuousLinearMap (RingHom.id ℝ) f).frameCoordinates
          (fun x hx ↦ ⟨hU hx, hU' hx⟩)
          ⟨ϕ, (TauCeti.contMDiff_hom_bundle_iff ϕ).2 hϕ⟩)
        (e.frameCoordinates hU s) := by
  let := VectorBundle.isTopologicalAddGroup ℝ G W
  let := VectorBundle.continuousSMul ℝ G W
  let A : Cₛ^n⟮I; F →L[ℝ] G, (fun x ↦ V x →L[ℝ] W x)⟯ :=
    ⟨ϕ, (TauCeti.contMDiff_hom_bundle_iff ϕ).2 hϕ⟩
  ext x
  rw [ContMDiffMap.clmApplyLinearMap_apply]
  have hf := Bundle.Trivialization.frameCoordinates_apply f hU'
    (mapLinearMap (fun x ↦ (ϕ x).toLinearMap) hϕ s) x
  rw [mapLinearMap_apply] at hf
  refine hf.trans (Eq.symm ?_)
  calc
    _ = ((e.continuousLinearMap (RingHom.id ℝ) f) ⟨(x : M), ϕ x⟩).2
        (e ⟨(x : M), s x⟩).2 :=
      congrArg₂ (fun (L : F →L[ℝ] G) (v : F) ↦ L v)
        (Bundle.Trivialization.frameCoordinates_apply
          (e.continuousLinearMap (RingHom.id ℝ) f) (fun x hx ↦ ⟨hU hx, hU' hx⟩) A x)
        (Bundle.Trivialization.frameCoordinates_apply e hU s x)
    _ = (f ⟨(x : M), ϕ x (s x)⟩).2 := by
      rw [Bundle.Trivialization.continuousLinearMap_apply]
      simp only [ContinuousLinearMap.comp_apply]
      rw [e.symmL_apply (hU x.2), e.symm_apply_apply_mk (hU x.2),
        f.continuousLinearMapAt_apply_of_mem ℝ (hU' x.2)]

variable {ι : Type*} (e : ι → Trivialization F (π F V))
  [∀ i, MemTrivializationAtlas (e i)]
  (f : ι → Trivialization G (π G W)) [∀ i, MemTrivializationAtlas (f i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)
  (hU' : ∀ i, (U i : Set M) ⊆ (f i).baseSet)

/-- Smooth bundle maps induce continuous maps for the compact derivative section topologies.
The chosen frame domains need not cover the base, provided the two systems use the same domains.
For covering systems these are the intrinsic, frame-independent section topologies. -/
theorem continuous_mapLinearMap_frameTopology :
    letI := frameTopology (I := I) (n := n) e U hU
    letI := frameTopology (I := I) (n := n) f U hU'
    Continuous (mapLinearMap (fun x ↦ (ϕ x).toLinearMap) hϕ) := by
  let := frameTopology (I := I) (n := n) e U hU
  let := frameTopology (I := I) (n := n) f U hU'
  apply (continuous_frameTopology_iff_frameCoordinates f U hU').2
  intro i
  let := VectorBundle.isTopologicalAddGroup ℝ G W
  let := VectorBundle.continuousSMul ℝ G W
  have h := (ContMDiffMap.continuous_clmApplyLinearMap
    (((e i).continuousLinearMap (RingHom.id ℝ) (f i)).frameCoordinates
      (fun x hx ↦ ⟨hU i hx, hU' i hx⟩)
      ⟨ϕ, (TauCeti.contMDiff_hom_bundle_iff ϕ).2 hϕ⟩)).comp
    (continuous_frameCoordinates e U hU i)
  exact h.congr fun s ↦ (frameCoordinates_mapLinearMap ϕ hϕ (e i) (f i)
    (hU i) (hU' i) s).symm

/-- Transport is continuous on every fixed-support subspace, for arbitrary supporting sets. -/
theorem continuous_mapSupportedIn (K : Set M) :
    letI := frameTopology (I := I) (n := n) e U hU
    letI := frameTopology (I := I) (n := n) f U hU'
    Continuous (mapSupportedIn (fun x ↦ (ϕ x).toLinearMap) hϕ K) := by
  let := frameTopology (I := I) (n := n) e U hU
  let := frameTopology (I := I) (n := n) f U hU'
  apply continuous_induced_rng.2
  simpa only [Function.comp_def, coe_mapSupportedIn] using
    ((continuous_mapLinearMap_frameTopology ϕ hϕ e f U hU hU').comp
      (continuous_subtype_val : Continuous (Subtype.val : supportedIn I F n V K → _)))

end ContMDiffSection
