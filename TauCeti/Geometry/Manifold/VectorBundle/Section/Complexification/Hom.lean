/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Complexification.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Map
public import TauCeti.Geometry.Manifold.VectorBundle.Section.CompactSupport.Complexification
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Distribution

/-!
# Complexified Hom coefficients on smooth sections and native test sections

`ContMDiffSection.homComplexificationEquiv` identifies complexified real Hom sections
with complex-linear Hom sections. The identification preserves support and compact stages
at every differentiability order. `TauCeti.BundleTest.homComplexificationCLE` is the real
continuous linear equivalence for the existing native smooth test-section topologies.

The fibre models may be incomplete or infinite dimensional. The native test topology
requires a locally compact base model and smooth bundles; no boundaryless assumption is used.
Specializing the target bundle to `DensityBundle I M` gives density-valued test coefficients,
without introducing a complex scalar action on the native test-section carrier.
-/

public section

noncomputable section
open Bundle FiberBundle Set TauCeti ContMDiffSection
open scoped TensorProduct ContDiff Manifold Topology

namespace ContMDiffSection
universe uM uF uG uV uL uE uH
variable {M : Type uM} [TopologicalSpace M]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type uG} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {V : M → Type uV} {L : M → Type uL}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  [∀ x, AddCommGroup (L x)] [∀ x, Module ℝ (L x)] [∀ x, TopologicalSpace (L x)]
  [TopologicalSpace (TotalSpace G L)] [FiberBundle G L] [VectorBundle ℝ G L]
  [∀ x, TopologicalSpace (ℂ ⊗[ℝ] V x)] [∀ x, IsComplexificationTopology (V x)]
  [∀ x, TopologicalSpace (ℂ ⊗[ℝ] L x)] [∀ x, IsComplexificationTopology (L x)]
  [∀ x, IsTopologicalAddGroup (L x)] [∀ x, ContinuousSMul ℝ (L x)]
  [∀ x, TopologicalSpace (ℂ ⊗[ℝ] (V x →L[ℝ] L x))]
  [∀ x, IsComplexificationTopology (V x →L[ℝ] L x)]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [ChartedSpace H M] {n : ℕ∞ω}

/-- Complexification of real bundle Hom sections as complex-linear Hom sections. -/
def homComplexificationEquiv :
    Cₛ^n⟮I; Complexification (F →L[ℝ] G), fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x)⟯ ≃ₗ[ℝ]
      Cₛ^n⟮I; Complexification F →L[ℂ] Complexification G,
        fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)⟯ :=
  mapEquiv (fun x ↦ (bundleHomComplexificationEquiv (F := F) (G := G) (V := V) (L := L)
    x).toLinearEquiv.restrictScalars ℝ)
    (by simpa only [LinearEquiv.restrictScalars_apply, ContinuousLinearEquiv.coe_toLinearEquiv]
      using
      (contMDiff_bundleHomComplexificationEquiv (F := F) (G := G) (V := V) (L := L) (IB := I) (n
        := n)))
    (by simpa only [LinearEquiv.restrictScalars_symm_apply,
      ContinuousLinearEquiv.coe_symm_toLinearEquiv] using
      (contMDiff_bundleHomComplexificationEquiv_symm (F := F) (G := G) (V := V) (L := L) (IB := I)
        (n := n)))

/-- The Hom coefficient identification on sections supported in any given set. -/
def SupportedIn.homComplexificationEquiv (K : Set M) :
    supportedIn I (Complexification (F →L[ℝ] G)) n
      (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x)) K ≃ₗ[ℝ]
    supportedIn I (Complexification F →L[ℂ] Complexification G) n
      (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)) K :=
  mapSupportedInEquiv (I := I) (n := n)
    (F := Complexification (F →L[ℝ] G))
    (G := Complexification F →L[ℂ] Complexification G)
    (V := fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x))
    (W := fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x))
    (fun x ↦ (bundleHomComplexificationEquiv (F := F) (G := G) (V := V) (L := L)
      x).toLinearEquiv.restrictScalars ℝ)
    (by simpa only [LinearEquiv.restrictScalars_apply, ContinuousLinearEquiv.coe_toLinearEquiv]
      using
      (contMDiff_bundleHomComplexificationEquiv (F := F) (G := G) (V := V) (L := L) (IB := I) (n
        := n)))
    (by simpa only [LinearEquiv.restrictScalars_symm_apply,
      ContinuousLinearEquiv.coe_symm_toLinearEquiv] using
      (contMDiff_bundleHomComplexificationEquiv_symm (F := F) (G := G) (V := V) (L := L) (IB := I)
        (n := n))) K

/-- The Hom coefficient identification on compactly supported sections. -/
def CompactlySupported.homComplexificationEquiv :
    compactlySupported I (Complexification (F →L[ℝ] G)) n
      (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x)) ≃ₗ[ℝ]
    compactlySupported I (Complexification F →L[ℂ] Complexification G) n
      (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)) :=
  mapCompactlySupportedEquiv (fun x ↦ (bundleHomComplexificationEquiv (F := F) (G := G) (V := V)
    (L := L) x).toLinearEquiv.restrictScalars ℝ)
    (by simpa only [LinearEquiv.restrictScalars_apply, ContinuousLinearEquiv.coe_toLinearEquiv]
      using
      (contMDiff_bundleHomComplexificationEquiv (F := F) (G := G) (V := V) (L := L) (IB := I) (n
        := n)))
    (by simpa only [LinearEquiv.restrictScalars_symm_apply,
      ContinuousLinearEquiv.coe_symm_toLinearEquiv] using
      (contMDiff_bundleHomComplexificationEquiv_symm (F := F) (G := G) (V := V) (L := L) (IB := I)
        (n := n)))

/-- The section equivalence is the existing fibrewise Hom complexification map. -/
@[simp]
theorem homComplexificationEquiv_apply (s :
    Cₛ^n⟮I; Complexification (F →L[ℝ] G), fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x)⟯) (x : M) :
    homComplexificationEquiv (F := F) (G := G) s x =
      bundleHomComplexificationEquiv (F := F) (G := G) x (s x) := by
  simp only [homComplexificationEquiv, mapEquiv_apply,
    LinearEquiv.restrictScalars_apply, ContinuousLinearEquiv.coe_toLinearEquiv]

/-- The coefficient identification preserves topological support exactly. -/
@[simp]
theorem homComplexificationEquiv_tsupport (s :
    Cₛ^n⟮I; Complexification (F →L[ℝ] G), fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x)⟯) :
    (homComplexificationEquiv (F := F) (G := G) s).tsupport = s.tsupport :=
  tsupport_mapEquiv _ _ _ s

/-- Compactly supported coefficients have the same fibrewise formula. -/
@[simp]
theorem CompactlySupported.homComplexificationEquiv_apply (s : compactlySupported I
  (Complexification (F →L[ℝ] G)) n
    (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x))) (x : M) :
    (CompactlySupported.homComplexificationEquiv (F := F) (G := G) s).val x =
      bundleHomComplexificationEquiv (F := F) (G := G) x (s.val x) := by
  simp only [CompactlySupported.homComplexificationEquiv, coe_mapCompactlySupportedEquiv,
    mapEquiv_apply, LinearEquiv.restrictScalars_apply, ContinuousLinearEquiv.coe_toLinearEquiv]


/-- The inverse section equivalence is the inverse fibrewise Hom complexification map. -/
@[simp]
theorem homComplexificationEquiv_symm_apply (s :
    Cₛ^n⟮I; Complexification F →L[ℂ] Complexification G,
      fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)⟯) (x : M) :
    (homComplexificationEquiv (F := F) (G := G)).symm s x =
      (bundleHomComplexificationEquiv (F := F) (G := G) x).symm (s x) := by
  simp only [homComplexificationEquiv, mapEquiv_symm, mapEquiv_apply,
    LinearEquiv.restrictScalars_symm_apply, ContinuousLinearEquiv.coe_symm_toLinearEquiv]

/-- Real and imaginary compactly supported real Hom coefficients. -/
def CompactlySupported.homComplexificationEquivProd :
    compactlySupported I (Complexification F →L[ℂ] Complexification G) n
      (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)) ≃ₗ[ℝ]
    compactlySupported I (F →L[ℝ] G) n (fun x ↦ V x →L[ℝ] L x) ×
      compactlySupported I (F →L[ℝ] G) n (fun x ↦ V x →L[ℝ] L x) :=
  (CompactlySupported.homComplexificationEquiv (I := I) (n := n) (F := F) (G := G) (V := V) (L :=
    L)).symm.trans
    (CompactlySupported.complexificationEquivProd (I := I) (n := n)
      (F := F →L[ℝ] G) (V := fun x ↦ V x →L[ℝ] L x))

/-- The compact-support identification preserves topological support exactly. -/
@[simp]
theorem CompactlySupported.homComplexificationEquiv_tsupport (s : compactlySupported I
  (Complexification (F →L[ℝ] G)) n
    (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x))) :
    (CompactlySupported.homComplexificationEquiv (F := F) (G := G) s).val.tsupport =
      s.val.tsupport := by
  simpa only [CompactlySupported.homComplexificationEquiv, coe_mapCompactlySupportedEquiv,
    ContMDiffSection.homComplexificationEquiv] using
      ContMDiffSection.homComplexificationEquiv_tsupport s.val

/-- The coefficient identification commutes with the native compact-stage inclusion. -/
theorem CompactlySupported.homComplexificationEquiv_ofSupportedIn (K : TopologicalSpace.Compacts M)
    (s : supportedIn I (Complexification (F →L[ℝ] G)) n
      (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x)) K) :
    CompactlySupported.homComplexificationEquiv (F := F) (G := G) (ofSupportedIn K s) =
      ofSupportedIn K (SupportedIn.homComplexificationEquiv (I := I) (n := n) (F := F) (G := G)
        (V := V) (L := L) (K : Set M) s) := by
  apply Subtype.ext
  apply ContMDiffSection.ext
  intro x
  simp only [CompactlySupported.homComplexificationEquiv_apply, ofSupportedIn_apply,
    SupportedIn.homComplexificationEquiv, coe_mapSupportedInEquiv, mapEquiv_apply,
    LinearEquiv.restrictScalars_apply, ContinuousLinearEquiv.coe_toLinearEquiv]

theorem CompactlySupported.homComplexificationEquiv_smulI
    (s : compactlySupported I (Complexification (F →L[ℝ] G)) n
      (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x))) (x : M) :
    (CompactlySupported.homComplexificationEquiv (F := F) (G := G)
      (CompactlySupported.smulIEquiv (I := I) (n := n) s)).val x =
      Complex.I • (CompactlySupported.homComplexificationEquiv (F := F) (G := G) s).val x := by
  rw [CompactlySupported.homComplexificationEquiv_apply,
    CompactlySupported.homComplexificationEquiv_apply,
    bundleHomComplexificationEquiv_coe]
  change homComplexificationLinearEquiv
    ((CompactlySupported.smulIEquiv s).val x) = Complex.I • homComplexificationLinearEquiv (s.val x)
  rw [CompactlySupported.smulIEquiv_apply]
  exact map_smul homComplexificationLinearEquiv Complex.I _

theorem CompactlySupported.homComplexificationEquiv_conj
    (s : compactlySupported I (Complexification (F →L[ℝ] G)) n
      (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x))) (x : M) (v : ℂ ⊗[ℝ] V x) :
    (CompactlySupported.homComplexificationEquiv (F := F) (G := G)
      (CompactlySupported.conjEquiv (I := I) (n := n) s)).val x (tmulConj (V x) v) =
      tmulConj (L x) ((CompactlySupported.homComplexificationEquiv (F := F) (G := G) s).val x v)
        := by
  rw [CompactlySupported.homComplexificationEquiv_apply,
    CompactlySupported.homComplexificationEquiv_apply,
    bundleHomComplexificationEquiv_coe]
  change homComplexificationLinearEquiv ((CompactlySupported.conjEquiv s).val x)
    (tmulConj (V x) v) = tmulConj (L x) (homComplexificationLinearEquiv (s.val x) v)
  rw [CompactlySupported.conjEquiv_apply]
  exact homComplexificationLinearEquiv_conj _ _

theorem CompactlySupported.homComplexificationEquiv_oneTmul_apply
    (s : compactlySupported I (F →L[ℝ] G) n (fun x ↦ V x →L[ℝ] L x))
    (x : M) (v : V x) :
    (CompactlySupported.homComplexificationEquiv (F := F) (G := G) (CompactlySupported.oneTmul
      s)).val x
      (1 ⊗ₜ[ℝ] v) = 1 ⊗ₜ[ℝ] (s.val x v) := by
  rw [CompactlySupported.homComplexificationEquiv_apply,
    bundleHomComplexificationEquiv_coe]
  change homComplexificationLinearEquiv ((CompactlySupported.oneTmul s).val x)
    (1 ⊗ₜ[ℝ] v) = 1 ⊗ₜ[ℝ] (s.val x v)
  simp only [CompactlySupported.coe_oneTmul, oneTmulLinearMap_apply,
    homComplexificationLinearEquiv_tmul_apply_tmul, one_mul]

theorem CompactlySupported.homComplexificationEquiv_realPoints_apply
    (s : compactlySupported I (F →L[ℝ] G) n (fun x ↦ V x →L[ℝ] L x))
    (x : M) (v : V x) :
    (CompactlySupported.homComplexificationEquiv (F := F) (G := G)
      (CompactlySupported.realPointsConjEquiv (I := I) (n := n) s).val).val x
        (1 ⊗ₜ[ℝ] v) = 1 ⊗ₜ[ℝ] (s.val x v) := by
  rw [CompactlySupported.coe_realPointsConjEquiv_apply]
  exact CompactlySupported.homComplexificationEquiv_oneTmul_apply s x v

section Frames
variable [ContMDiffVectorBundle n F V I] [ContMDiffVectorBundle n G L I]
  [IsManifold I n M]

private abbrev sourceFrame (a : M) :
    Trivialization (Complexification (F →L[ℝ] G))
      (π (Complexification (F →L[ℝ] G)) (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x))) :=
  trivializationAt (Complexification (F →L[ℝ] G))
    (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x)) a

private abbrev targetFrame (a : M) :
    Trivialization (Complexification F →L[ℂ] Complexification G)
      (π (Complexification F →L[ℂ] Complexification G)
        (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x))) :=
  trivializationAt (Complexification F →L[ℂ] Complexification G)
    (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)) a

private abbrev frameDomains (a : M) : TopologicalSpace.Opens M :=
  ⟨(trivializationAt F V a).baseSet ∩ (trivializationAt G L a).baseSet,
    (trivializationAt F V a).open_baseSet.inter (trivializationAt G L a).open_baseSet⟩

omit [∀ x, TopologicalSpace (ℂ ⊗[ℝ] V x)] [∀ x, TopologicalSpace (ℂ ⊗[ℝ] L x)]
  [∀ x, IsComplexificationTopology (V x)] [∀ x, IsComplexificationTopology (L x)] in
private theorem sourceDomain (a : M) :
    (frameDomains (F := F) (G := G) (V := V) (L := L) a : Set M) ⊆
      (sourceFrame (F := F) (G := G) (V := V) (L := L) a).baseSet := by
  simp only [sourceFrame, trivializationAt_complexification, hom_trivializationAt,
    Trivialization.baseSet_complexification, Trivialization.baseSet_continuousLinearMap]
  exact Subset.rfl

omit [∀ x, TopologicalSpace (ℂ ⊗[ℝ] (V x →L[ℝ] L x))]
  [∀ x, IsComplexificationTopology (V x →L[ℝ] L x)] in
private theorem targetDomain (a : M) :
    (frameDomains (F := F) (G := G) (V := V) (L := L) a : Set M) ⊆
      (targetFrame (F := F) (G := G) (V := V) (L := L) a).baseSet := by
  simp only [targetFrame, trivializationAt_complexification, hom_trivializationAt,
    Trivialization.baseSet_complexification, Trivialization.baseSet_continuousLinearMap]
  exact Subset.rfl

private theorem homComplexification_continuous :
    let := @ContMDiffSection.frameTopology ℝ inferInstance E inferInstance inferInstance H
      inferInstance I
      M inferInstance inferInstance (Complexification (F →L[ℝ] G)) inferInstance inferInstance
      (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x))
      (fun _ ↦ inferInstance) (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)
      inferInstance inferInstance inferInstance n inferInstance inferInstance M
      (sourceFrame (F := F) (G := G) (V := V) (L := L)) (fun _ ↦ inferInstance)
      (frameDomains (F := F) (G := G) (V := V) (L := L))
      (sourceDomain (F := F) (G := G) (V := V) (L := L))
    let := @ContMDiffSection.frameTopology ℝ inferInstance E inferInstance inferInstance H
      inferInstance I
      M inferInstance inferInstance (Complexification F →L[ℂ] Complexification G) inferInstance
        inferInstance
      (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x))
      (fun _ ↦ inferInstance) (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)
      inferInstance inferInstance inferInstance n inferInstance inferInstance M
      (targetFrame (F := F) (G := G) (V := V) (L := L)) (fun _ ↦ inferInstance)
      (frameDomains (F := F) (G := G) (V := V) (L := L))
      (targetDomain (F := F) (G := G) (V := V) (L := L))
    Continuous (homComplexificationEquiv (I := I) (n := n) (F := F) (G := G)
      (V := V) (L := L)) := by
  refine @continuous_frameTopology_of_frameCoordinates_eq_clm_apply ℝ inferInstance
    E inferInstance inferInstance H inferInstance I M inferInstance inferInstance
    (Complexification (F →L[ℝ] G)) inferInstance inferInstance
    (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x))
    (fun _ ↦ inferInstance) (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)
    inferInstance inferInstance inferInstance n inferInstance inferInstance M
    (sourceFrame (F := F) (G := G) (V := V) (L := L)) (fun _ ↦ inferInstance)
    (frameDomains (F := F) (G := G) (V := V) (L := L))
    (sourceDomain (F := F) (G := G) (V := V) (L := L))
    (Complexification F →L[ℂ] Complexification G) inferInstance inferInstance
    (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x))
    (fun _ ↦ inferInstance) (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)
    inferInstance inferInstance inferInstance inferInstance
    (targetFrame (F := F) (G := G) (V := V) (L := L)) (fun _ ↦ inferInstance)
    (targetDomain (F := F) (G := G) (V := V) (L := L))
    (homComplexificationEquiv (I := I) (n := n) (F := F) (G := G) (V := V) (L := L))
    (fun _ ↦ (Complexification.continuousLinearMapEquiv F G).toContinuousLinearMap.restrictScalars
      ℝ) ?_
  intro a s x
  have hx : (x : M) ∈ (trivializationAt F V a).baseSet ∩
      (trivializationAt G L a).baseSet := by
    exact x.property
  simpa only [Bundle.Trivialization.frameCoordinates_apply, homComplexificationEquiv_apply,
    sourceFrame, targetFrame, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearEquiv.coe_coe] using
    bundleHomComplexificationEquiv_in_trivializationAt (F := F) (G := G) (V := V) (L := L)
      a (x : M) hx (s x)

private theorem homComplexification_symm_continuous :
    let := @ContMDiffSection.frameTopology ℝ inferInstance E inferInstance inferInstance H
      inferInstance I
      M inferInstance inferInstance (Complexification F →L[ℂ] Complexification G) inferInstance
        inferInstance
      (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x))
      (fun _ ↦ inferInstance) (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)
      inferInstance inferInstance inferInstance n inferInstance inferInstance M
      (targetFrame (F := F) (G := G) (V := V) (L := L)) (fun _ ↦ inferInstance)
      (frameDomains (F := F) (G := G) (V := V) (L := L))
      (targetDomain (F := F) (G := G) (V := V) (L := L))
    let := @ContMDiffSection.frameTopology ℝ inferInstance E inferInstance inferInstance H
      inferInstance I
      M inferInstance inferInstance (Complexification (F →L[ℝ] G)) inferInstance inferInstance
      (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x))
      (fun _ ↦ inferInstance) (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)
      inferInstance inferInstance inferInstance n inferInstance inferInstance M
      (sourceFrame (F := F) (G := G) (V := V) (L := L)) (fun _ ↦ inferInstance)
      (frameDomains (F := F) (G := G) (V := V) (L := L))
      (sourceDomain (F := F) (G := G) (V := V) (L := L))
    Continuous (homComplexificationEquiv (I := I) (n := n) (F := F) (G := G)
      (V := V) (L := L)).symm := by
  refine @continuous_frameTopology_of_frameCoordinates_eq_clm_apply ℝ inferInstance
    E inferInstance inferInstance H inferInstance I M inferInstance inferInstance
    (Complexification F →L[ℂ] Complexification G) inferInstance inferInstance
    (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x))
    (fun _ ↦ inferInstance) (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)
    inferInstance inferInstance inferInstance n inferInstance inferInstance M
    (targetFrame (F := F) (G := G) (V := V) (L := L)) (fun _ ↦ inferInstance)
    (frameDomains (F := F) (G := G) (V := V) (L := L))
    (targetDomain (F := F) (G := G) (V := V) (L := L))
    (Complexification (F →L[ℝ] G)) inferInstance inferInstance
    (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x))
    (fun _ ↦ inferInstance) (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)
    inferInstance inferInstance inferInstance inferInstance
    (sourceFrame (F := F) (G := G) (V := V) (L := L)) (fun _ ↦ inferInstance)
    (sourceDomain (F := F) (G := G) (V := V) (L := L))
    (homComplexificationEquiv (I := I) (n := n) (F := F) (G := G) (V := V) (L := L)).symm
    (fun _ ↦ (Complexification.continuousLinearMapEquiv F
      G).symm.toContinuousLinearMap.restrictScalars ℝ) ?_
  intro a s x
  have hx : (x : M) ∈ (trivializationAt F V a).baseSet ∩
      (trivializationAt G L a).baseSet := by
    exact x.property
  simpa only [Bundle.Trivialization.frameCoordinates_apply, homComplexificationEquiv_symm_apply,
    targetFrame, sourceFrame, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearEquiv.coe_coe] using
    bundleHomComplexificationEquiv_symm_in_trivializationAt (F := F) (G := G) (V := V) (L := L)
      a (x : M) hx (s x)

/- The following private data are the existing native topology constructors.
They share the same typed preferred frames throughout the continuity proofs. -/
private abbrev homSourceSectionTopology :=
  @ContMDiffSection.frameTopology ℝ inferInstance E inferInstance inferInstance H inferInstance I
      M inferInstance inferInstance (Complexification (F →L[ℝ] G)) inferInstance inferInstance
      (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x))
      (fun _ ↦ inferInstance) (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)
      inferInstance inferInstance inferInstance n inferInstance inferInstance M
      (sourceFrame (F := F) (G := G) (V := V) (L := L)) (fun _ ↦ inferInstance)
      (frameDomains (F := F) (G := G) (V := V) (L := L))
      (sourceDomain (F := F) (G := G) (V := V) (L := L))

private abbrev homTargetSectionTopology :=
  @ContMDiffSection.frameTopology ℝ inferInstance E inferInstance inferInstance H inferInstance I
      M inferInstance inferInstance (Complexification F →L[ℂ] Complexification G) inferInstance
        inferInstance
      (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x))
      (fun _ ↦ inferInstance) (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)
      inferInstance inferInstance inferInstance n inferInstance inferInstance M
      (targetFrame (F := F) (G := G) (V := V) (L := L)) (fun _ ↦ inferInstance)
      (frameDomains (F := F) (G := G) (V := V) (L := L))
      (targetDomain (F := F) (G := G) (V := V) (L := L))

private abbrev homSourceCompactTopology :=
  @ContMDiffSection.compactlySupportedTopology E H M inferInstance inferInstance inferInstance I
      inferInstance inferInstance (Complexification (F →L[ℝ] G)) inferInstance inferInstance
      (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x))
      (fun _ ↦ inferInstance) (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)
      inferInstance inferInstance inferInstance n inferInstance inferInstance M
      (sourceFrame (F := F) (G := G) (V := V) (L := L)) (fun _ ↦ inferInstance)
      (frameDomains (F := F) (G := G) (V := V) (L := L))
      (sourceDomain (F := F) (G := G) (V := V) (L := L))

private abbrev homTargetCompactTopology :=
  @ContMDiffSection.compactlySupportedTopology E H M inferInstance inferInstance inferInstance I
      inferInstance inferInstance (Complexification F →L[ℂ] Complexification G) inferInstance
        inferInstance
      (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x))
      (fun _ ↦ inferInstance) (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)
      inferInstance inferInstance inferInstance n inferInstance inferInstance M
      (targetFrame (F := F) (G := G) (V := V) (L := L)) (fun _ ↦ inferInstance)
      (frameDomains (F := F) (G := G) (V := V) (L := L))
      (targetDomain (F := F) (G := G) (V := V) (L := L))

/-- The Hom coefficient equivalence for the native preferred-frame topologies on a support stage. -/
def SupportedIn.homComplexificationCLE (K : Set M) :
    let := (@ContMDiffSection.frameTopology ℝ inferInstance E inferInstance inferInstance H
      inferInstance I
      M inferInstance inferInstance (Complexification (F →L[ℝ] G)) inferInstance inferInstance
      (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x))
      (fun _ ↦ inferInstance) (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)
      inferInstance inferInstance inferInstance n inferInstance inferInstance M
      (fun a ↦ trivializationAt (Complexification (F →L[ℝ] G)) (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x)) a)
        (fun _ ↦ inferInstance)
      (fun a ↦ ⟨(trivializationAt F V a).baseSet ∩ (trivializationAt G L a).baseSet,
        (trivializationAt F V a).open_baseSet.inter (trivializationAt G L a).open_baseSet⟩)
      (fun a ↦ by
        simp only [trivializationAt_complexification, hom_trivializationAt,
          Trivialization.baseSet_complexification, Trivialization.baseSet_continuousLinearMap]
        exact Subset.rfl))
    let := (@ContMDiffSection.frameTopology ℝ inferInstance E inferInstance inferInstance H
      inferInstance I
      M inferInstance inferInstance (Complexification F →L[ℂ] Complexification G) inferInstance
        inferInstance
      (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x))
      (fun _ ↦ inferInstance) (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)
      inferInstance inferInstance inferInstance n inferInstance inferInstance M
      (fun a ↦ trivializationAt (Complexification F →L[ℂ] Complexification G) (fun x ↦ (ℂ ⊗[ℝ] V
        x) →L[ℂ] (ℂ ⊗[ℝ] L x)) a) (fun _ ↦ inferInstance)
      (fun a ↦ ⟨(trivializationAt F V a).baseSet ∩ (trivializationAt G L a).baseSet,
        (trivializationAt F V a).open_baseSet.inter (trivializationAt G L a).open_baseSet⟩)
      (fun a ↦ by
        simp only [trivializationAt_complexification, hom_trivializationAt,
          Trivialization.baseSet_complexification, Trivialization.baseSet_continuousLinearMap]
        exact Subset.rfl))
    supportedIn I (Complexification (F →L[ℝ] G)) n
      (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x)) K ≃L[ℝ]
    supportedIn I (Complexification F →L[ℂ] Complexification G) n
      (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)) K := by
  let := homSourceSectionTopology (I := I) (n := n) (F := F) (G := G) (V := V) (L := L)
  let := homTargetSectionTopology (I := I) (n := n) (F := F) (G := G) (V := V) (L := L)
  refine { SupportedIn.homComplexificationEquiv (I := I) (n := n) (F := F) (G := G) (V := V) (L :=
    L) K with
    continuous_toFun := ?_, continuous_invFun := ?_ }
  · apply continuous_induced_rng.2
    have hf : Continuous (fun s : supportedIn I (Complexification (F →L[ℝ] G)) n
        (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x)) K ↦
        ContMDiffSection.homComplexificationEquiv (I := I) (n := n) (F := F) (G := G)
          (V := V) (L := L) s.val) :=
      (homComplexification_continuous (I := I) (n := n) (F := F) (G := G)
        (V := V) (L := L)).comp continuous_subtypeVal
    simpa only [SupportedIn.homComplexificationEquiv, coe_mapSupportedInEquiv,
      LinearEquiv.coe_toEquiv, LinearEquiv.toFun_eq_coe, LinearMap.toFun_eq_coe,
      LinearEquiv.coe_coe, ContMDiffSection.homComplexificationEquiv, Function.comp_def] using hf
  · apply continuous_induced_rng.2
    have hf : Continuous (fun s : supportedIn I (Complexification F →L[ℂ] Complexification G) n
        (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)) K ↦
        (ContMDiffSection.homComplexificationEquiv (I := I) (n := n) (F := F) (G := G)
          (V := V) (L := L)).symm s.val) :=
      (homComplexification_symm_continuous (I := I) (n := n) (F := F) (G := G)
        (V := V) (L := L)).comp continuous_subtypeVal
    refine hf.congr fun s ↦ ?_
    ext x
    simp only [SupportedIn.homComplexificationEquiv, LinearEquiv.invFun_eq_symm,
      Function.comp_apply, coe_mapSupportedInEquiv_symm,
      ContMDiffSection.homComplexificationEquiv, mapEquiv_symm, mapEquiv_apply]

private theorem homComplexificationCompact_continuous :
    let := homSourceCompactTopology (I := I) (n := n) (F := F) (G := G) (V := V) (L := L)
    let := homTargetCompactTopology (I := I) (n := n) (F := F) (G := G) (V := V) (L := L)
    Continuous (CompactlySupported.homComplexificationEquiv (I := I) (n := n) (F := F) (G := G) (V
      := V) (L := L)) := by
  let : ∀ a : M, MemTrivializationAtlas
      (sourceFrame (F := F) (G := G) (V := V) (L := L) a) := fun _ ↦ inferInstance
  let : ∀ a : M, MemTrivializationAtlas
      (targetFrame (F := F) (G := G) (V := V) (L := L) a) := fun _ ↦ inferInstance
  let := homSourceSectionTopology (I := I) (n := n) (F := F) (G := G) (V := V) (L := L)
  let := homTargetSectionTopology (I := I) (n := n) (F := F) (G := G) (V := V) (L := L)
  let := homSourceCompactTopology (I := I) (n := n) (F := F) (G := G) (V := V) (L := L)
  let := homTargetCompactTopology (I := I) (n := n) (F := F) (G := G) (V := V) (L := L)
  let := isTopologicalAddGroup_compactlySupportedTopology (I := I) (n := n)
    (targetFrame (F := F) (G := G) (V := V) (L := L))
    (frameDomains (F := F) (G := G) (V := V) (L := L))
    (targetDomain (F := F) (G := G) (V := V) (L := L))
  let := continuousSMul_compactlySupportedTopology (I := I) (n := n)
    (targetFrame (F := F) (G := G) (V := V) (L := L))
    (frameDomains (F := F) (G := G) (V := V) (L := L))
    (targetDomain (F := F) (G := G) (V := V) (L := L))
  let := locallyConvexSpace_compactlySupportedTopology (I := I) (n := n)
    (targetFrame (F := F) (G := G) (V := V) (L := L))
    (frameDomains (F := F) (G := G) (V := V) (L := L))
    (targetDomain (F := F) (G := G) (V := V) (L := L))
  apply (continuous_compactlySupportedTopology_iff (I := I) (n := n)
    (sourceFrame (F := F) (G := G) (V := V) (L := L))
    (frameDomains (F := F) (G := G) (V := V) (L := L))
    (sourceDomain (F := F) (G := G) (V := V) (L := L))
    ((CompactlySupported.homComplexificationEquiv (I := I) (n := n) (F := F) (G := G) (V := V) (L
      := L)).toLinearMap)).2
  intro K
  have hc := ContMDiffSection.continuous_ofSupportedIn (I := I) (n := n)
      (targetFrame (F := F) (G := G) (V := V) (L := L))
      (frameDomains (F := F) (G := G) (V := V) (L := L))
      (targetDomain (F := F) (G := G) (V := V) (L := L)) K
  exact (hc.comp (SupportedIn.homComplexificationCLE (I := I) (n := n) (F := F) (G := G) (V := V)
    (L := L) (K : Set M)).continuous).congr fun s ↦
      (CompactlySupported.homComplexificationEquiv_ofSupportedIn K s).symm

private theorem homComplexificationCompact_symm_continuous :
    let := homTargetCompactTopology (I := I) (n := n) (F := F) (G := G) (V := V) (L := L)
    let := homSourceCompactTopology (I := I) (n := n) (F := F) (G := G) (V := V) (L := L)
    Continuous (CompactlySupported.homComplexificationEquiv (I := I) (n := n) (F := F) (G := G) (V
      := V) (L := L)).symm := by
  let : ∀ a : M, MemTrivializationAtlas
      (sourceFrame (F := F) (G := G) (V := V) (L := L) a) := fun _ ↦ inferInstance
  let : ∀ a : M, MemTrivializationAtlas
      (targetFrame (F := F) (G := G) (V := V) (L := L) a) := fun _ ↦ inferInstance
  let := homSourceSectionTopology (I := I) (n := n) (F := F) (G := G) (V := V) (L := L)
  let := homTargetSectionTopology (I := I) (n := n) (F := F) (G := G) (V := V) (L := L)
  let := homSourceCompactTopology (I := I) (n := n) (F := F) (G := G) (V := V) (L := L)
  let := homTargetCompactTopology (I := I) (n := n) (F := F) (G := G) (V := V) (L := L)
  let := isTopologicalAddGroup_compactlySupportedTopology (I := I) (n := n)
    (sourceFrame (F := F) (G := G) (V := V) (L := L))
    (frameDomains (F := F) (G := G) (V := V) (L := L))
    (sourceDomain (F := F) (G := G) (V := V) (L := L))
  let := continuousSMul_compactlySupportedTopology (I := I) (n := n)
    (sourceFrame (F := F) (G := G) (V := V) (L := L))
    (frameDomains (F := F) (G := G) (V := V) (L := L))
    (sourceDomain (F := F) (G := G) (V := V) (L := L))
  let := locallyConvexSpace_compactlySupportedTopology (I := I) (n := n)
    (sourceFrame (F := F) (G := G) (V := V) (L := L))
    (frameDomains (F := F) (G := G) (V := V) (L := L))
    (sourceDomain (F := F) (G := G) (V := V) (L := L))
  apply (continuous_compactlySupportedTopology_iff (I := I) (n := n)
    (targetFrame (F := F) (G := G) (V := V) (L := L))
    (frameDomains (F := F) (G := G) (V := V) (L := L))
    (targetDomain (F := F) (G := G) (V := V) (L := L))
    ((CompactlySupported.homComplexificationEquiv (I := I) (n := n) (F := F) (G := G) (V := V) (L
      := L)).symm.toLinearMap)).2
  intro K
  have hc := ContMDiffSection.continuous_ofSupportedIn (I := I) (n := n)
      (sourceFrame (F := F) (G := G) (V := V) (L := L))
      (frameDomains (F := F) (G := G) (V := V) (L := L))
      (sourceDomain (F := F) (G := G) (V := V) (L := L)) K
  exact (hc.comp (SupportedIn.homComplexificationCLE (I := I) (n := n) (F := F) (G := G) (V := V)
    (L := L) (K : Set M)).symm.continuous).congr fun s ↦ by
    dsimp only [Function.comp_apply]
    simp only [LinearEquiv.coe_coe]
    apply (CompactlySupported.homComplexificationEquiv (I := I) (n := n)
      (F := F) (G := G) (V := V) (L := L)).injective
    rw [LinearEquiv.apply_symm_apply,
      CompactlySupported.homComplexificationEquiv_ofSupportedIn]
    exact congrArg (ofSupportedIn K)
      ((SupportedIn.homComplexificationCLE (I := I) (n := n) (F := F) (G := G)
        (V := V) (L := L) (K : Set M)).apply_symm_apply s)

/-- The Hom coefficient equivalence for the native final locally convex compact-support
  topologies. -/
def CompactlySupported.homComplexificationCLE :
    let := (@ContMDiffSection.compactlySupportedTopology E H M inferInstance inferInstance
      inferInstance I
      inferInstance inferInstance (Complexification (F →L[ℝ] G)) inferInstance inferInstance
      (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x))
      (fun _ ↦ inferInstance) (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)
      inferInstance inferInstance inferInstance n inferInstance inferInstance M
      (fun a ↦ trivializationAt (Complexification (F →L[ℝ] G)) (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x)) a)
        (fun _ ↦ inferInstance)
      (fun a ↦ ⟨(trivializationAt F V a).baseSet ∩ (trivializationAt G L a).baseSet,
        (trivializationAt F V a).open_baseSet.inter (trivializationAt G L a).open_baseSet⟩)
      (fun a ↦ by
        simp only [trivializationAt_complexification, hom_trivializationAt,
          Trivialization.baseSet_complexification, Trivialization.baseSet_continuousLinearMap]
        exact Subset.rfl))
    let := (@ContMDiffSection.compactlySupportedTopology E H M inferInstance inferInstance
      inferInstance I
      inferInstance inferInstance (Complexification F →L[ℂ] Complexification G) inferInstance
        inferInstance
      (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x))
      (fun _ ↦ inferInstance) (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)
      inferInstance inferInstance inferInstance n inferInstance inferInstance M
      (fun a ↦ trivializationAt (Complexification F →L[ℂ] Complexification G) (fun x ↦ (ℂ ⊗[ℝ] V
        x) →L[ℂ] (ℂ ⊗[ℝ] L x)) a) (fun _ ↦ inferInstance)
      (fun a ↦ ⟨(trivializationAt F V a).baseSet ∩ (trivializationAt G L a).baseSet,
        (trivializationAt F V a).open_baseSet.inter (trivializationAt G L a).open_baseSet⟩)
      (fun a ↦ by
        simp only [trivializationAt_complexification, hom_trivializationAt,
          Trivialization.baseSet_complexification, Trivialization.baseSet_continuousLinearMap]
        exact Subset.rfl))
    compactlySupported I (Complexification (F →L[ℝ] G)) n (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x)) ≃L[ℝ]
      compactlySupported I (Complexification F →L[ℂ] Complexification G) n (fun x ↦ (ℂ ⊗[ℝ] V x)
        →L[ℂ] (ℂ ⊗[ℝ] L x)) := by
  let := homSourceCompactTopology (I := I) (n := n) (F := F) (G := G) (V := V) (L := L)
  let := homTargetCompactTopology (I := I) (n := n) (F := F) (G := G) (V := V) (L := L)
  exact { CompactlySupported.homComplexificationEquiv (I := I) (n := n) (F := F) (G := G) (V := V)
    (L := L) with
    continuous_toFun := homComplexificationCompact_continuous,
    continuous_invFun := homComplexificationCompact_symm_continuous }

omit [∀ x, TopologicalSpace (ℂ ⊗[ℝ] V x)] [∀ x, TopologicalSpace (ℂ ⊗[ℝ] L x)]
  [∀ x, TopologicalSpace (ℂ ⊗[ℝ] (V x →L[ℝ] L x))]
  [NormedSpace ℝ F] [NormedSpace ℝ G] [VectorBundle ℝ F V] [VectorBundle ℝ G L]
  [∀ x, Module ℝ (V x)] [∀ x, AddCommGroup (V x)] [∀ x, AddCommGroup (L x)] [∀ x, Module ℝ (L x)]
  [∀ x, IsTopologicalAddGroup (L x)] [∀ x, ContinuousSMul ℝ (L x)]
  [∀ x, IsComplexificationTopology (V x)] [∀ x, IsComplexificationTopology (L x)]
  [∀ x, IsComplexificationTopology (V x →L[ℝ] L x)] in
private theorem frameDomains_cover (x : M) : ∃ a, x ∈ frameDomains (F := F) (G := G) (V := V) (L
  := L) a :=
  ⟨x, mem_baseSet_trivializationAt F V x, mem_baseSet_trivializationAt G L x⟩

section Tests
variable [LocallyCompactSpace E]
  [ContMDiffVectorBundle ∞ F V I] [ContMDiffVectorBundle ∞ G L I] [IsManifold I ∞ M]

private def homComplexificationTests :
    BundleTest I (Complexification (F →L[ℝ] G))
      (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x)) ≃ₗ[ℝ]
    BundleTest I (Complexification F →L[ℂ] Complexification G)
      (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)) :=
  ((BundleTest.ofCompactlySupported I (Complexification (F →L[ℝ] G))
      (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x))).symm.trans
    (CompactlySupported.homComplexificationEquiv (I := I) (n := ∞) (F := F) (G := G) (V := V) (L
      := L))).trans
    (BundleTest.ofCompactlySupported I (Complexification F →L[ℂ] Complexification G)
      (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)))

/-- Hom coefficients as a real continuous linear equivalence of native smooth test-section
  spaces. -/
def _root_.TauCeti.BundleTest.homComplexificationCLE :
    BundleTest I (Complexification (F →L[ℝ] G))
      (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x)) ≃L[ℝ]
    BundleTest I (Complexification F →L[ℂ] Complexification G)
      (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)) := by
  have hs := @BundleTest.instTopologicalSpace_eq_compactlySupportedTopology E H M
    inferInstance inferInstance inferInstance I inferInstance inferInstance
    (Complexification (F →L[ℝ] G)) inferInstance inferInstance (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x))
    (fun _ ↦ inferInstance) (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance M
    (sourceFrame (F := F) (G := G) (V := V) (L := L)) (fun _ ↦ inferInstance)
    (frameDomains (F := F) (G := G) (V := V) (L := L))
    (sourceDomain (F := F) (G := G) (V := V) (L := L))
    (frameDomains_cover (F := F) (G := G) (V := V) (L := L))
  have ht := @BundleTest.instTopologicalSpace_eq_compactlySupportedTopology E H M
    inferInstance inferInstance inferInstance I inferInstance inferInstance
    (Complexification F →L[ℂ] Complexification G) inferInstance inferInstance (fun x ↦ (ℂ ⊗[ℝ] V
      x) →L[ℂ] (ℂ ⊗[ℝ] L x))
    (fun _ ↦ inferInstance) (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance M
    (targetFrame (F := F) (G := G) (V := V) (L := L)) (fun _ ↦ inferInstance)
    (frameDomains (F := F) (G := G) (V := V) (L := L))
    (targetDomain (F := F) (G := G) (V := V) (L := L))
    (frameDomains_cover (F := F) (G := G) (V := V) (L := L))
  refine { homComplexificationTests (I := I) (F := F) (G := G) (V := V) (L := L) with
    continuous_toFun := ?_, continuous_invFun := ?_ }
  · change @Continuous _ _ BundleTest.instTopologicalSpace BundleTest.instTopologicalSpace
      (CompactlySupported.homComplexificationEquiv (I := I) (n := ∞) (F := F) (G := G) (V := V) (L
        := L))
    rw [hs, ht]
    exact ContMDiffSection.homComplexificationCompact_continuous
  · change @Continuous _ _ BundleTest.instTopologicalSpace BundleTest.instTopologicalSpace
      (CompactlySupported.homComplexificationEquiv (I := I) (n := ∞) (F := F) (G := G) (V := V) (L
        := L)).symm
    rw [hs, ht]
    exact ContMDiffSection.homComplexificationCompact_symm_continuous

theorem _root_.TauCeti.BundleTest.homComplexificationCLE_apply
    (s : BundleTest I (Complexification (F →L[ℝ] G))
      (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x))) (x : M) :
    TauCeti.BundleTest.homComplexificationCLE (I := I) (F := F) (G := G) s x =
      bundleHomComplexificationEquiv (F := F) (G := G) (V := V) (L := L) x (s x) := by
  simp only [TauCeti.BundleTest.homComplexificationCLE, homComplexificationTests,
    ContinuousLinearEquiv.coe_mk, LinearEquiv.trans_apply, BundleTest.coe_ofCompactlySupported,
    CompactlySupported.homComplexificationEquiv_apply]

theorem _root_.TauCeti.BundleTest.homComplexificationCLE_closedSupport
    (s : BundleTest I (Complexification (F →L[ℝ] G))
      (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x))) :
    closure {x | TauCeti.BundleTest.homComplexificationCLE (I := I) (F := F) (G := G) s x ≠ 0} =
      closure {x | s x ≠ 0} := by
  congr 1
  ext x
  change (BundleTest.homComplexificationCLE (I := I) (F := F) (G := G) s x ≠ 0 ↔ s x ≠ 0)
  rw [BundleTest.homComplexificationCLE_apply, bundleHomComplexificationEquiv_coe]
  change homComplexificationLinearEquiv (s x) ≠ 0 ↔ s x ≠ 0
  constructor
  · intro h hz
    apply h
    rw [hz, map_zero]
  · intro h hz
    apply h
    apply (homComplexificationLinearEquiv (W := V x) (D := L x)).injective
    rw [hz, map_zero]

end Tests
end Frames
end ContMDiffSection
