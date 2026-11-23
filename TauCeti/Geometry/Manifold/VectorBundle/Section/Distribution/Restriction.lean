/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.ExtendByZero.Topology
public import TauCeti.Geometry.Manifold.VectorBundle.Density.OpenSubset
import TauCeti.Geometry.Manifold.ContMDiff.Subtype

/-!
# Restriction of native bundle distributions

Intrinsic dual-density tests extend across an open inclusion by the smooth tangent-density
comparison and native extension by zero. Transposition gives restriction on the existing
compact-convergence distribution carrier. The nested-open law compares independently formed
intrinsic restrictions on the actual double pullback with direct restriction.
-/

public noncomputable section

open Bundle FiberBundle Filter Set Topology TopologicalSpace ContMDiffSection
open scoped Manifold ContDiff TauCeti.ManifoldWeakWhitney CompactConvergenceCLM

namespace TauCeti.BundleTest
attribute [local instance] openPullbackSmooth


section Density
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {U : Opens M}

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]

private abbrev openInclusion : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
private abbrev localCoefficients := fun x : U ↦
  ((openInclusion (U := U) *ᵖ V) x →L[ℝ] TauCeti.DensityBundle I U x)
private abbrev ambientCoefficients := fun x : M ↦ V x →L[ℝ] TauCeti.DensityBundle I M x
private abbrev pulledAmbientCoefficients :=
  openInclusion (U := U) *ᵖ (ambientCoefficients (I := I) (V := V))
private abbrev intrinsicFrame (x : U) :=
  trivializationAt (F →L[ℝ] ℝ) (localCoefficients (I := I) (V := V) (U := U)) x
private abbrev pulledFrame (x : U) :=
  (trivializationAt (F →L[ℝ] ℝ) (ambientCoefficients (I := I) (V := V)) (x : M)).pullback
    (openInclusion (U := U))

private def coefficientFrameDomain (x : U) : Opens U :=
  ⟨(intrinsicFrame (I := I) (F := F) (V := V) x).baseSet ∩
    (pulledFrame (I := I) (F := F) (V := V) x).baseSet ∩
    interior {y | ∀ ℓ : localCoefficients (I := I) (V := V) (U := U) y,
      (trivializationAt (F →L[ℝ] ℝ) (ambientCoefficients (I := I) (V := V)) (x : M)
        ⟨(y : M), TauCeti.DensityBundle.openHomEquiv y ℓ⟩).2 =
      (intrinsicFrame (I := I) (F := F) (V := V) x ⟨y, ℓ⟩).2},
    ((intrinsicFrame (I := I) (F := F) (V := V) x).open_baseSet.inter
      (pulledFrame (I := I) (F := F) (V := V) x).open_baseSet).inter isOpen_interior⟩

omit [ContMDiffVectorBundle ∞ F V I] in
private theorem mem_coefficientFrameDomain (x : U) :
    x ∈ coefficientFrameDomain (I := I) (F := F) (V := V) x := by
  refine ⟨⟨mem_baseSet_trivializationAt _ _ _, ?_⟩,
    mem_interior_iff_mem_nhds.mpr
      (TauCeti.DensityBundle.eventually_openHom_frame_eq (I := I) (F := F) (V := V) x)⟩
  simpa only [pulledFrame, Trivialization.pullback_baseSet, openInclusion,
    ContinuousMap.coe_mk, Set.mem_preimage] using
    (mem_baseSet_trivializationAt (F →L[ℝ] ℝ)
      (ambientCoefficients (I := I) (V := V)) (x : M))

private theorem continuous_coefficientMap_frame :
    let A := coefficientFrameDomain (I := I) (F := F) (V := V) (U := U)
    let e := intrinsicFrame (I := I) (F := F) (V := V) (U := U)
    let e' := pulledFrame (I := I) (F := F) (V := V) (U := U)
    let hA : ∀ x, (A x : Set U) ⊆ (e x).baseSet := fun _ _ h ↦ h.1.1
    let hA' : ∀ x, (A x : Set U) ⊆ (e' x).baseSet := fun _ _ h ↦ h.1.2
    letI := frameTopology (I := I) (n := ∞) e A hA
    letI := frameTopology (I := I) (n := ∞) e' A hA'
    Continuous (mapLinearMap (I := I) (F := F →L[ℝ] ℝ) (G := F →L[ℝ] ℝ)
      (V := localCoefficients (I := I) (V := V) (U := U))
      (W := pulledAmbientCoefficients (I := I) (V := V) (U := U))
      (fun x ↦ (TauCeti.DensityBundle.openHomEquiv (I := I) (V := V) x).toLinearEquiv.toLinearMap)
      (TauCeti.DensityBundle.contMDiff_openHomToPullback (I := I) (F := F) (V := V))) := by
  apply continuous_frameTopology_of_frameCoordinates_eq_clm_apply
    (intrinsicFrame (I := I) (F := F) (V := V))
    (coefficientFrameDomain (I := I) (F := F) (V := V))
    (fun _ _ h ↦ h.1.1) (pulledFrame (I := I) (F := F) (V := V))
    (fun _ _ h ↦ h.1.2) (fun _ ↦ ContinuousLinearMap.id ℝ (F →L[ℝ] ℝ))
  intro i s y
  simp only [ContinuousLinearMap.id_apply]
  erw [Trivialization.frameCoordinates_apply, Trivialization.frameCoordinates_apply,
    mapLinearMap_apply, Trivialization.pullback_apply]
  change (trivializationAt (F →L[ℝ] ℝ) (ambientCoefficients (I := I) (V := V)) (i : M)
      ⟨(y.val : M), TauCeti.DensityBundle.openHomEquiv y.val (s y.val)⟩).2 =
    (intrinsicFrame (I := I) (F := F) (V := V) i ⟨y.val, s y.val⟩).2
  exact (interior_subset y.property.2) (s y.val)

private theorem continuous_coefficientInverse_frame :
    let A := coefficientFrameDomain (I := I) (F := F) (V := V) (U := U)
    let e := pulledFrame (I := I) (F := F) (V := V) (U := U)
    let e' := intrinsicFrame (I := I) (F := F) (V := V) (U := U)
    let hA : ∀ x, (A x : Set U) ⊆ (e x).baseSet := fun _ _ h ↦ h.1.2
    let hA' : ∀ x, (A x : Set U) ⊆ (e' x).baseSet := fun _ _ h ↦ h.1.1
    letI := frameTopology (I := I) (n := ∞) e A hA
    letI := frameTopology (I := I) (n := ∞) e' A hA'
    Continuous (mapLinearMap (I := I) (F := F →L[ℝ] ℝ) (G := F →L[ℝ] ℝ)
      (V := pulledAmbientCoefficients (I := I) (V := V) (U := U))
      (W := localCoefficients (I := I) (V := V) (U := U))
      (fun x ↦ (TauCeti.DensityBundle.openHomEquiv (I := I) (V := V)
        x).symm.toLinearEquiv.toLinearMap)
      (TauCeti.DensityBundle.contMDiff_openHomFromPullback (I := I) (F := F) (V := V))) := by
  apply continuous_frameTopology_of_frameCoordinates_eq_clm_apply
    (pulledFrame (I := I) (F := F) (V := V))
    (coefficientFrameDomain (I := I) (F := F) (V := V))
    (fun _ _ h ↦ h.1.2) (intrinsicFrame (I := I) (F := F) (V := V))
    (fun _ _ h ↦ h.1.1) (fun _ ↦ ContinuousLinearMap.id ℝ (F →L[ℝ] ℝ))
  intro i s y
  simp only [ContinuousLinearMap.id_apply]
  erw [Trivialization.frameCoordinates_apply, Trivialization.frameCoordinates_apply,
    mapLinearMap_apply, Trivialization.pullback_apply]
  change (intrinsicFrame (I := I) (F := F) (V := V) i
      ⟨y.val, (TauCeti.DensityBundle.openHomEquiv y.val).symm (s y.val)⟩).2 =
    (trivializationAt (F →L[ℝ] ℝ) (ambientCoefficients (I := I) (V := V)) (i : M)
      ⟨(y.val : M), s y.val⟩).2
  refine ((interior_subset y.property.2) ((TauCeti.DensityBundle.openHomEquiv y.val).symm (s
    y.val))).symm.trans ?_
  exact congrArg (fun ℓ : ambientCoefficients (I := I) (V := V) (y.val : M) ↦
    (trivializationAt (F →L[ℝ] ℝ) (ambientCoefficients (I := I) (V := V)) (i : M)
      ⟨(y.val : M), ℓ⟩).2) ((TauCeti.DensityBundle.openHomEquiv y.val).apply_symm_apply (s y.val))

private theorem intrinsicFrameTopology_common_eq :
    let e := intrinsicFrame (I := I) (F := F) (V := V) (U := U)
    let A := coefficientFrameDomain (I := I) (F := F) (V := V) (U := U)
    frameTopology (I := I) (n := ∞) e A (fun _ _ h ↦ h.1.1) =
      frameTopology (I := I) (n := ∞) e
        (fun x ↦ ⟨(e x).baseSet, (e x).open_baseSet⟩) (fun _ ↦ subset_rfl) := by
  intro e A
  exact frameTopology_eq_of_covers (I := I) (n := ∞) e A (fun _ _ h ↦ h.1.1)
    (fun x ↦ ⟨x, mem_coefficientFrameDomain x⟩) e
    (fun x ↦ ⟨(e x).baseSet, (e x).open_baseSet⟩) (fun _ ↦ subset_rfl)
    (fun x ↦ ⟨x, mem_baseSet_trivializationAt (F →L[ℝ] ℝ)
      (localCoefficients (I := I) (V := V) (U := U)) x⟩)

private theorem pulledFrameTopology_common_eq :
    let eB := pulledFrame (I := I) (F := F) (V := V) (U := U)
    let e' := trivializationAt (F →L[ℝ] ℝ)
      (pulledAmbientCoefficients (I := I) (V := V) (U := U))
    let A := coefficientFrameDomain (I := I) (F := F) (V := V) (U := U)
    frameTopology (I := I) (n := ∞) eB A (fun _ _ h ↦ h.1.2) =
      frameTopology (I := I) (n := ∞) e'
        (fun x ↦ ⟨(e' x).baseSet, (e' x).open_baseSet⟩) (fun _ ↦ subset_rfl) := by
  intro eB e' A
  exact frameTopology_eq_of_covers (I := I) (n := ∞) eB A (fun _ _ h ↦ h.1.2)
    (fun x ↦ ⟨x, mem_coefficientFrameDomain x⟩) e'
    (fun x ↦ ⟨(e' x).baseSet, (e' x).open_baseSet⟩) (fun _ ↦ subset_rfl)
    (fun x ↦ ⟨x, mem_baseSet_trivializationAt (F →L[ℝ] ℝ)
      (pulledAmbientCoefficients (I := I) (V := V) (U := U)) x⟩)

/-- The intrinsic-to-pulled-back density comparison on an arbitrary fixed support stage,
for the existing preferred-frame topologies. -/
def openDensityHomSupportedInCLE (K : Set U) :
    let e := (trivializationAt (F →L[ℝ] ℝ) (fun x : U ↦ ((⟨Subtype.val, continuous_subtypeVal⟩ :
      C(U, M)) *ᵖ V) x →L[ℝ] TauCeti.DensityBundle I U x))
    let e' := (trivializationAt (F →L[ℝ] ℝ) ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ
      (fun x : M ↦ V x →L[ℝ] TauCeti.DensityBundle I M x)))
    let := frameTopology (I := I) (n := ∞) e
      (fun x ↦ ⟨(e x).baseSet, (e x).open_baseSet⟩) (fun _ ↦ subset_rfl)
    let := frameTopology (I := I) (n := ∞) e'
      (fun x ↦ ⟨(e' x).baseSet, (e' x).open_baseSet⟩) (fun _ ↦ subset_rfl)
    supportedIn I (F →L[ℝ] ℝ) ∞ ((fun x : U ↦ ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ
      V) x →L[ℝ] TauCeti.DensityBundle I U x)) K ≃L[ℝ]
      supportedIn I (F →L[ℝ] ℝ) ∞ (((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ (fun x : M
        ↦ V x →L[ℝ] TauCeti.DensityBundle I M x))) K := by
  intro e e'
  letI := frameTopology (I := I) (n := ∞) e
    (fun x ↦ ⟨(e x).baseSet, (e x).open_baseSet⟩) (fun _ ↦ subset_rfl)
  letI := frameTopology (I := I) (n := ∞) e'
    (fun x ↦ ⟨(e' x).baseSet, (e' x).open_baseSet⟩) (fun _ ↦ subset_rfl)
  let eB := pulledFrame (I := I) (F := F) (V := V) (U := U)
  let A := coefficientFrameDomain (I := I) (F := F) (V := V) (U := U)
  let hA : ∀ x, (A x : Set U) ⊆ (e x).baseSet := fun _ _ h ↦ h.1.1
  let hA' : ∀ x, (A x : Set U) ⊆ (eB x).baseSet := fun _ _ h ↦ h.1.2
  have hT := intrinsicFrameTopology_common_eq (I := I) (F := F) (V := V) (U := U)
  have hT' := pulledFrameTopology_common_eq (I := I) (F := F) (V := V) (U := U)
  let L := mapSupportedInEquiv (I := I) (F := F →L[ℝ] ℝ) (G := F →L[ℝ] ℝ)
    (V := localCoefficients (I := I) (V := V) (U := U))
    (W := pulledAmbientCoefficients (I := I) (V := V) (U := U))
    (fun x ↦ (TauCeti.DensityBundle.openHomEquiv (I := I) (V := V) x).toLinearEquiv)
    (TauCeti.DensityBundle.contMDiff_openHomToPullback (I := I) (F := F) (V := V))
    (TauCeti.DensityBundle.contMDiff_openHomFromPullback (I := I) (F := F) (V := V)) K
  refine { L with continuous_toFun := ?_, continuous_invFun := ?_ }
  · erw [← hT, ← hT']
    let := frameTopology (I := I) (n := ∞) e A hA
    let := frameTopology (I := I) (n := ∞) eB A hA'
    have hv : Continuous (fun z : supportedIn I (F →L[ℝ] ℝ) ∞
        (localCoefficients (I := I) (V := V) (U := U)) K ↦ (L z).val) := by
      convert (continuous_coefficientMap_frame (I := I) (F := F) (V := V)).comp
        (continuous_subtypeVal : Continuous (fun z : supportedIn I (F →L[ℝ] ℝ) ∞
          (localCoefficients (I := I) (V := V) (U := U)) K ↦ z.val)) using 1
      funext z
      ext x
      erw [coe_mapSupportedInEquiv, mapEquiv_apply, mapLinearMap_apply]
      rfl
    exact hv.subtype_mk _
  · erw [← hT', ← hT]
    let := frameTopology (I := I) (n := ∞) e A hA
    let := frameTopology (I := I) (n := ∞) eB A hA'
    have hv : Continuous (fun z : supportedIn I (F →L[ℝ] ℝ) ∞
        (pulledAmbientCoefficients (I := I) (V := V) (U := U)) K ↦ (L.symm z).val) := by
      convert (continuous_coefficientInverse_frame (I := I) (F := F) (V := V)).comp
        (continuous_subtypeVal : Continuous (fun z : supportedIn I (F →L[ℝ] ℝ) ∞
          (pulledAmbientCoefficients (I := I) (V := V) (U := U)) K ↦ z.val)) using 1
      funext z
      ext x
      erw [coe_mapSupportedInEquiv_symm, mapEquiv_symm, mapEquiv_apply, mapLinearMap_apply]
      rfl
    exact hv.subtype_mk _

variable [T2Space M]

private def densityTestLinearEquiv :
    TauCeti.BundleTest I (F →L[ℝ] ℝ) (localCoefficients (I := I) (V := V) (U := U)) ≃ₗ[ℝ]
      TauCeti.BundleTest I (F →L[ℝ] ℝ) (pulledAmbientCoefficients (I := I) (V := V) (U := U)) :=
  (TauCeti.BundleTest.ofCompactlySupported I (F →L[ℝ] ℝ) _).symm.trans
    ((mapCompactlySupportedEquiv (I := I) (F := F →L[ℝ] ℝ) (G := F →L[ℝ] ℝ)
      (V := localCoefficients (I := I) (V := V) (U := U))
      (W := pulledAmbientCoefficients (I := I) (V := V) (U := U))
      (fun x ↦ (TauCeti.DensityBundle.openHomEquiv (I := I) (V := V) x).toLinearEquiv)
      (TauCeti.DensityBundle.contMDiff_openHomToPullback (I := I) (F := F) (V := V))
      (TauCeti.DensityBundle.contMDiff_openHomFromPullback (I := I) (F := F) (V := V))).trans
      (TauCeti.BundleTest.ofCompactlySupported I (F →L[ℝ] ℝ) _))

omit [T2Space M] [ContMDiffVectorBundle ∞ F V I] in
/-- The intrinsic test comparison evaluates by the native pointwise open-density map. -/
private theorem densityTestLinearEquiv_apply
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) ((fun x : U ↦ ((⟨Subtype.val, continuous_subtypeVal⟩ :
      C(U, M)) *ᵖ V) x →L[ℝ] TauCeti.DensityBundle I U x)))
    (x : U) : densityTestLinearEquiv (I := I) (F := F) (V := V) s x =
      TauCeti.DensityBundle.openHomEquiv x (s x) := by
  change (mapCompactlySupportedEquiv (I := I) (F := F →L[ℝ] ℝ) (G := F →L[ℝ] ℝ)
    (V := localCoefficients (I := I) (V := V) (U := U))
    (W := pulledAmbientCoefficients (I := I) (V := V) (U := U))
    (fun x ↦ (TauCeti.DensityBundle.openHomEquiv (I := I) (V := V) x).toLinearEquiv)
    (TauCeti.DensityBundle.contMDiff_openHomToPullback (I := I) (F := F) (V := V))
    (TauCeti.DensityBundle.contMDiff_openHomFromPullback (I := I) (F := F) (V := V))
    ((ofCompactlySupported I (F →L[ℝ] ℝ) _).symm s)).val x = _
  erw [coe_mapCompactlySupportedEquiv, mapEquiv_apply]
  rfl

omit [T2Space M] [ContMDiffVectorBundle ∞ F V I] in
/-- The inverse intrinsic test comparison evaluates by the inverse native density map. -/
private theorem densityTestLinearEquiv_symm_apply
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) (((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ
      (fun x : M ↦ V x →L[ℝ] TauCeti.DensityBundle I M x))))
    (x : U) : (densityTestLinearEquiv (I := I) (F := F) (V := V)).symm s x =
      (TauCeti.DensityBundle.openHomEquiv x).symm (s x) := by
  change ((mapCompactlySupportedEquiv (I := I) (F := F →L[ℝ] ℝ) (G := F →L[ℝ] ℝ)
    (V := localCoefficients (I := I) (V := V) (U := U))
    (W := pulledAmbientCoefficients (I := I) (V := V) (U := U))
    (fun x ↦ (TauCeti.DensityBundle.openHomEquiv (I := I) (V := V) x).toLinearEquiv)
    (TauCeti.DensityBundle.contMDiff_openHomToPullback (I := I) (F := F) (V := V))
    (TauCeti.DensityBundle.contMDiff_openHomFromPullback (I := I) (F := F) (V := V))).symm
    ((ofCompactlySupported I (F →L[ℝ] ℝ) _).symm s)).val x = _
  erw [coe_mapCompactlySupportedEquiv_symm, mapEquiv_symm, mapEquiv_apply]
  rfl


/-- Intrinsic dual-density tests identify continuously with tests valued in the pullback
of the ambient dual-density bundle. -/
def openDensityHomCLE :
    TauCeti.BundleTest I (F →L[ℝ] ℝ) ((fun x : U ↦ ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U,
      M)) *ᵖ V) x →L[ℝ] TauCeti.DensityBundle I U x)) ≃L[ℝ]
      TauCeti.BundleTest I (F →L[ℝ] ℝ) (((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ (fun
        x : M ↦ V x →L[ℝ] TauCeti.DensityBundle I M x))) := by
  let e := intrinsicFrame (I := I) (F := F) (V := V) (U := U)
  let e' := trivializationAt (F →L[ℝ] ℝ)
    (pulledAmbientCoefficients (I := I) (V := V) (U := U))
  letI := frameTopology (I := I) (n := ∞) e
    (fun x ↦ ⟨(e x).baseSet, (e x).open_baseSet⟩) (fun _ ↦ subset_rfl)
  letI := frameTopology (I := I) (n := ∞) e'
    (fun x ↦ ⟨(e' x).baseSet, (e' x).open_baseSet⟩) (fun _ ↦ subset_rfl)
  let eqv := fun x : U ↦ (TauCeti.DensityBundle.openHomEquiv (I := I) (V := V) x).toLinearEquiv
  let hf := TauCeti.DensityBundle.contMDiff_openHomToPullback (I := I) (F := F) (V := V) (U := U)
  let hg := TauCeti.DensityBundle.contMDiff_openHomFromPullback (I := I) (F := F) (V := V) (U := U)
  refine { densityTestLinearEquiv (I := I) (F := F) (V := V) (U := U) with
    continuous_toFun := ?_, continuous_invFun := ?_ }
  · apply (TauCeti.BundleTest.continuous_iff_continuous_comp
      (densityTestLinearEquiv (I := I) (F := F) (V := V) (U := U)).toLinearMap).2
    intro K
    convert (TauCeti.BundleTest.continuous_ofSupportedIn K).comp
      (openDensityHomSupportedInCLE (I := I) (F := F) (V := V) K).continuous using 1
    funext z
    apply TauCeti.BundleTest.ext
    intro x
    simp only [Function.comp_apply]
    erw [densityTestLinearEquiv_apply]
    simp only [LinearEquiv.symm_apply_apply, ofSupportedIn_apply]
    change _ = (mapSupportedInEquiv
      (I := I) (F := F →L[ℝ] ℝ) (G := F →L[ℝ] ℝ)
      (V := localCoefficients (I := I) (V := V) (U := U))
      (W := pulledAmbientCoefficients (I := I) (V := V) (U := U)) eqv hf hg K z).val x
    erw [coe_mapSupportedInEquiv, mapEquiv_apply]
    rfl
  · apply (TauCeti.BundleTest.continuous_iff_continuous_comp
      (densityTestLinearEquiv (I := I) (F := F) (V := V) (U := U)).symm.toLinearMap).2
    intro K
    convert (TauCeti.BundleTest.continuous_ofSupportedIn K).comp
      (openDensityHomSupportedInCLE (I := I) (F := F) (V := V) K).symm.continuous using 1
    funext z
    apply TauCeti.BundleTest.ext
    intro x
    simp only [Function.comp_apply]
    erw [densityTestLinearEquiv_symm_apply]
    simp only [LinearEquiv.symm_apply_apply, ofSupportedIn_apply]
    change _ = ((mapSupportedInEquiv
      (I := I) (F := F →L[ℝ] ℝ) (G := F →L[ℝ] ℝ)
      (V := localCoefficients (I := I) (V := V) (U := U))
      (W := pulledAmbientCoefficients (I := I) (V := V) (U := U)) eqv hf hg K).symm z).val x
    erw [coe_mapSupportedInEquiv_symm, mapEquiv_symm, mapEquiv_apply]
    rfl

omit [T2Space M] in
/-- The intrinsic test comparison evaluates by the native pointwise open-density map. -/
theorem openDensityHomCLE_apply
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) ((fun x : U ↦ ((⟨Subtype.val, continuous_subtypeVal⟩ :
      C(U, M)) *ᵖ V) x →L[ℝ] TauCeti.DensityBundle I U x)))
    (x : U) : openDensityHomCLE (I := I) (F := F) (V := V) s x =
      TauCeti.DensityBundle.openHomEquiv x (s x) := by
  exact densityTestLinearEquiv_apply s x

omit [T2Space M] in
/-- The inverse intrinsic test comparison evaluates by the inverse native density map. -/
theorem openDensityHomCLE_symm_apply
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) (((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ
      (fun x : M ↦ V x →L[ℝ] TauCeti.DensityBundle I M x))))
    (x : U) : (openDensityHomCLE (I := I) (F := F) (V := V)).symm s x =
      (TauCeti.DensityBundle.openHomEquiv x).symm (s x) := by
  exact densityTestLinearEquiv_symm_apply s x

omit [T2Space M] in
/-- The intrinsic density comparison commutes with multiplication by smooth real functions. -/
theorem openDensityHomCLE_smulLeftCLM (f : C^∞⟮I, U; ℝ⟯)
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) ((fun x : U ↦ ((⟨Subtype.val, continuous_subtypeVal⟩ :
      C(U, M)) *ᵖ V) x →L[ℝ] TauCeti.DensityBundle I U x))) :
    openDensityHomCLE (I := I) (F := F) (V := V) (TauCeti.BundleTest.smulLeftCLM f s) =
      TauCeti.BundleTest.smulLeftCLM f (openDensityHomCLE (I := I) (F := F) (V := V) s) := by
  apply TauCeti.BundleTest.ext
  intro x
  let Φ := TauCeti.DensityBundle.openHomEquiv (I := I) (V := V) x
  have hL := openDensityHomCLE_apply (I := I) (F := F) (V := V)
    (smulLeftCLM (I := I) (F := F →L[ℝ] ℝ)
      (V := localCoefficients (I := I) (V := V) (U := U)) f s) x
  have hS := smulLeftCLM_apply (I := I) (F := F →L[ℝ] ℝ)
    (V := localCoefficients (I := I) (V := V) (U := U)) f s x
  have hR := smulLeftCLM_apply (I := I) (F := F →L[ℝ] ℝ)
    (V := pulledAmbientCoefficients (I := I) (V := V) (U := U)) f
    (openDensityHomCLE (I := I) (F := F) (V := V) s) x
  have hE := openDensityHomCLE_apply (I := I) (F := F) (V := V) s x
  exact hL.trans ((congrArg Φ hS).trans ((Φ.map_smul (f x) (s x)).trans
    ((congrArg (fun v ↦ f x • v) hE.symm).trans hR.symm)))

end Density
end TauCeti.BundleTest

namespace TauCeti.BundleDistribution
open TauCeti.BundleTest
attribute [local instance] TauCeti.BundleTest.openPullbackSmooth
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [IsManifold I ∞ M] {U : Opens M}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]

/-- Extend intrinsic dual-density tests by zero after the native tangent-density comparison. -/
def testExtensionCLM :
    TauCeti.BundleTest I (F →L[ℝ] ℝ) ((fun x : U ↦ ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U,
      M)) *ᵖ V) x →L[ℝ] TauCeti.DensityBundle I U x)) →L[ℝ]
      TauCeti.BundleTest I (F →L[ℝ] ℝ) ((fun x : M ↦ V x →L[ℝ] TauCeti.DensityBundle I M x)) := by
  exact (TauCeti.BundleTest.extendByZeroCLM (I := I) (F := F →L[ℝ] ℝ)
    (V := ambientCoefficients (I := I) (V := V)) (U := U)).comp
    (openDensityHomCLE (I := I) (F := F) (V := V) (U := U)).toContinuousLinearMap

/-- On the open subset, intrinsic extension evaluates by the native density comparison. -/
theorem testExtensionCLM_apply_of_mem
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) ((fun x : U ↦ ((⟨Subtype.val, continuous_subtypeVal⟩ :
      C(U, M)) *ᵖ V) x →L[ℝ] TauCeti.DensityBundle I U x)))
    (x : U) : testExtensionCLM (I := I) (F := F) (V := V) s (x : M) =
      TauCeti.DensityBundle.openHomEquiv x (s x) := by
  change TauCeti.BundleTest.extendByZeroCLM
    (I := I) (F := F →L[ℝ] ℝ) (V := ambientCoefficients (I := I) (V := V)) (U := U)
    (openDensityHomCLE (I := I) (F := F) (V := V) s) (x : M) = _
  erw [TauCeti.BundleTest.extendByZeroCLM_apply_of_mem]
  exact openDensityHomCLE_apply s x

/-- Intrinsic test extension vanishes outside the open subset. -/
theorem testExtensionCLM_apply_of_notMem
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) ((fun x : U ↦ ((⟨Subtype.val, continuous_subtypeVal⟩ :
      C(U, M)) *ᵖ V) x →L[ℝ] TauCeti.DensityBundle I U x)))
    {x : M} (hx : x ∉ U) : testExtensionCLM (I := I) (F := F) (V := V) s x = 0 := by
  change TauCeti.BundleTest.extendByZeroCLM (I := I) (F := F →L[ℝ] ℝ)
    (V := ambientCoefficients (I := I) (V := V)) (U := U)
    (openDensityHomCLE (I := I) (F := F) (V := V) s) x = 0
  exact TauCeti.BundleTest.extendByZeroCLM_apply_of_notMem (I := I) (F := F →L[ℝ] ℝ)
    (V := ambientCoefficients (I := I) (V := V))
    (openDensityHomCLE (I := I) (F := F) (V := V) s) hx

/-- Restriction of native bundle distributions, obtained by compact-convergence transpose
of intrinsic dual-density test extension. -/
def restrictCLM :
    let c : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    TauCeti.BundleDistribution I M F V →L[ℝ] TauCeti.BundleDistribution I U F (c *ᵖ V) := by
  dsimp only
  exact (testExtensionCLM (I := I) (F := F) (V := V) (U := U)).precompCompactConvergenceCLM ℝ

/-- Restriction pairs with an intrinsic test by pairing with its ambient extension. -/
theorem restrictCLM_apply :
    ∀ (T : TauCeti.BundleDistribution I M F V)
      (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) ((fun x : U ↦ ((⟨Subtype.val, continuous_subtypeVal⟩ :
        C(U, M)) *ᵖ V) x →L[ℝ] TauCeti.DensityBundle I U x))),
      restrictCLM (I := I) (F := F) (V := V) T s =
        T (testExtensionCLM (I := I) (F := F) (V := V) s) := by
  intro T s
  rfl

/-- A point mass inside the open subset restricts by transposing the native density map. -/
theorem restrictCLM_delta_of_mem :
    ∀ (x : U) (ℓ : (fun x : M ↦ V x →L[ℝ] TauCeti.DensityBundle I M x) (x : M) →L[ℝ] ℝ),
      restrictCLM (I := I) (F := F) (V := V) (U := U)
        (TauCeti.BundleTest.delta (I := I) (F := F →L[ℝ] ℝ) (x : M) ℓ) =
      TauCeti.BundleTest.delta (I := I) (F := F →L[ℝ] ℝ)
        (V := fun y : U ↦ ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V) y →L[ℝ]
          TauCeti.DensityBundle I U y) x
        (ℓ.comp (TauCeti.DensityBundle.openHomEquiv (I := I) (V := V) x).toContinuousLinearMap) :=
          by
  intro x ℓ
  apply ContinuousLinearMap.ext
  intro s
  erw [restrictCLM_apply, TauCeti.BundleTest.delta_apply,
    testExtensionCLM_apply_of_mem s x, TauCeti.BundleTest.delta_apply]
  rfl

/-- A point mass outside the open subset restricts to zero. -/
theorem restrictCLM_delta_of_notMem :
    ∀ (x : M) (_hx : x ∉ U) (ℓ : (fun x : M ↦ V x →L[ℝ] TauCeti.DensityBundle I M x) x →L[ℝ] ℝ),
      restrictCLM (I := I) (F := F) (V := V) (U := U)
        (TauCeti.BundleTest.delta (I := I) (F := F →L[ℝ] ℝ) x ℓ) = 0 := by
  intro x hx ℓ
  apply ContinuousLinearMap.ext
  intro s
  erw [restrictCLM_apply, TauCeti.BundleTest.delta_apply,
    testExtensionCLM_apply_of_notMem s hx, map_zero]
  rfl

/-- The topological support of intrinsic test extension is exactly the included support. -/
theorem tsupport_testExtensionCLM
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) ((fun x : U ↦ ((⟨Subtype.val, continuous_subtypeVal⟩ :
      C(U, M)) *ᵖ V) x →L[ℝ] TauCeti.DensityBundle I U x))) :
    closure {x : M | testExtensionCLM (I := I) (F := F) (V := V) s x ≠ 0} =
      Subtype.val '' closure {x : U | s x ≠ 0} := by
  change closure {x : M | TauCeti.BundleTest.extendByZeroCLM (I := I) (F := F →L[ℝ] ℝ)
      (V := ambientCoefficients (I := I) (V := V)) (U := U)
      (openDensityHomCLE (I := I) (F := F) (V := V) s) x ≠ 0} = _
  trans Subtype.val '' closure {x : U | openDensityHomCLE (I := I) (F := F) (V := V) s x ≠ 0}
  · exact TauCeti.BundleTest.tsupport_extendByZeroCLM (I := I) (F := F →L[ℝ] ℝ)
      (V := ambientCoefficients (I := I) (V := V)) (U := U)
      (openDensityHomCLE (I := I) (F := F) (V := V) s)
  · congr 2
    ext x
    change (openDensityHomCLE (I := I) (F := F) (V := V) s x ≠ 0) ↔ (s x ≠ 0)
    erw [openDensityHomCLE_apply]
    exact not_congr (TauCeti.DensityBundle.openHomEquiv (I := I) (V := V) x).map_eq_zero_iff

/-- Intrinsic test extension commutes with the restriction of a smooth ambient multiplier. -/
theorem testExtensionCLM_smulLeftCLM (f : C^∞⟮I, M; ℝ⟯)
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) ((fun x : U ↦ ((⟨Subtype.val, continuous_subtypeVal⟩ :
      C(U, M)) *ᵖ V) x →L[ℝ] TauCeti.DensityBundle I U x))) :
    testExtensionCLM (I := I) (F := F) (V := V) (TauCeti.BundleTest.smulLeftCLM (f.restrict U) s) =
      TauCeti.BundleTest.smulLeftCLM f (testExtensionCLM (I := I) (F := F) (V := V) s) := by
  change TauCeti.BundleTest.extendByZeroCLM (I := I) (F := F →L[ℝ] ℝ)
      (V := ambientCoefficients (I := I) (V := V)) (U := U)
      (openDensityHomCLE (I := I) (F := F) (V := V) (TauCeti.BundleTest.smulLeftCLM (f.restrict U)
        s)) = _
  rw [openDensityHomCLE_smulLeftCLM]
  exact TauCeti.BundleTest.extendByZeroCLM_smulLeftCLM f _

/-- Native distribution restriction commutes with smooth real multiplication. -/
theorem restrictCLM_smulLeftDualCLM :
    ∀ (f : C^∞⟮I, M; ℝ⟯) (T : TauCeti.BundleDistribution I M F V),
      restrictCLM (I := I) (F := F) (V := V) (U := U)
        (TauCeti.BundleTest.smulLeftDualCLM (I := I) (F := F →L[ℝ] ℝ)
          (V := (fun x : M ↦ V x →L[ℝ] TauCeti.DensityBundle I M x)) f T) =
      TauCeti.BundleTest.smulLeftDualCLM (I := I) (F := F →L[ℝ] ℝ)
        (V := (fun x : U ↦ ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V) x →L[ℝ]
          TauCeti.DensityBundle I U x)) (f.restrict U)
        (restrictCLM (I := I) (F := F) (V := V) (U := U) T) := by
  intro f T
  apply ContinuousLinearMap.ext
  intro s
  erw [restrictCLM_apply, smulLeftDualCLM_apply, smulLeftDualCLM_apply,
    restrictCLM_apply]
  exact congrArg T (testExtensionCLM_smulLeftCLM (I := I) (F := F) (V := V) f s).symm

private def intrinsicInclusionCLM {D : Opens M} (h : U ≤ D) :
    TauCeti.BundleTest I (F →L[ℝ] ℝ) (localCoefficients (I := I) (V := V) (U := U)) →L[ℝ]
      TauCeti.BundleTest I (F →L[ℝ] ℝ) (localCoefficients (I := I) (V := V) (U := D)) := by
  exact (openDensityHomCLE (I := I) (F := F) (V := V) (U := D)).symm.toContinuousLinearMap.comp
    ((TauCeti.BundleTest.inclusionCLM (I := I) (F := F →L[ℝ] ℝ)
      (V := ambientCoefficients (I := I) (V := V)) h).comp
      (openDensityHomCLE (I := I) (F := F) (V := V) (U := U)).toContinuousLinearMap)

private abbrev nestedOpen (U D : Opens M) : Opens D :=
  Opens.comap (⟨Subtype.val, continuous_subtypeVal⟩ : C(D, M)) U

/-- The actual iterated open subset identifies smoothly with the direct smaller open subset. -/
def nestedBaseDiffeomorph {D : Opens M} (h : U ≤ D) :
    (Opens.comap (⟨Subtype.val, continuous_subtypeVal⟩ : C(D, M)) U) ≃ₘ^∞⟮I, I⟯ U where
  toFun x := ⟨x.val.val, x.property⟩
  invFun u := ⟨⟨u.val, h u.property⟩, u.property⟩
  left_inv x := by cases x; rfl
  right_inv u := by cases u; rfl
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff U _).mp
    exact (contMDiff_subtypeVal (I := I) (U := D)).comp
      (contMDiff_subtypeVal (I := I) (U := nestedOpen U D))
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff (nestedOpen U D) _).mp
    apply (ContMDiff.subtypeVal_comp_iff D _).mp
    exact contMDiff_subtypeVal

private abbrev doubleCoefficients (D : Opens M) := fun x : nestedOpen U D ↦
  (((openInclusion (M := D) (U := nestedOpen U D)) *ᵖ
    ((openInclusion (U := D)) *ᵖ V)) x →L[ℝ]
    TauCeti.DensityBundle I (nestedOpen U D) x)

private def iteratedIntrinsicTestExtensionCLM (D : Opens M) :
    TauCeti.BundleTest I (F →L[ℝ] ℝ) (doubleCoefficients (I := I) (V := V) (U := U) D) →L[ℝ]
      TauCeti.BundleTest I (F →L[ℝ] ℝ) (ambientCoefficients (I := I) (V := V)) :=
  (testExtensionCLM (I := I) (F := F) (V := V) (U := D)).comp
    (testExtensionCLM (I := I) (F := F) (M := D)
      (V := (openInclusion (U := D)) *ᵖ V) (U := nestedOpen U D))

private theorem tsupport_iteratedIntrinsicTestExtensionCLM {D : Opens M} (h : U ≤ D)
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) (doubleCoefficients (I := I) (V := V) (U := U) D)) :
    closure {x : M | iteratedIntrinsicTestExtensionCLM (I := I) (F := F) (V := V) D s x ≠ 0} =
      Subtype.val '' (nestedBaseDiffeomorph (I := I) h) '' closure {x : nestedOpen U D | s x ≠ 0}
        := by
  change closure {x : M | testExtensionCLM (I := I) (F := F) (V := V) (U := D)
    (testExtensionCLM (I := I) (F := F) (M := D)
      (V := (openInclusion (U := D)) *ᵖ V) (U := nestedOpen U D) s) x ≠ 0} = _
  erw [tsupport_testExtensionCLM (I := I) (F := F) (V := V) (U := D)]
  erw [tsupport_testExtensionCLM (I := I) (F := F) (M := D)
    (V := (openInclusion (U := D)) *ᵖ V) (U := nestedOpen U D)]
  rw [Set.image_image, Set.image_image]
  rfl

private def intrinsicNestedTestComparisonCLM {D : Opens M} (h : U ≤ D) :
    TauCeti.BundleTest I (F →L[ℝ] ℝ) (doubleCoefficients (I := I) (V := V) (U := U) D) →L[ℝ]
      TauCeti.BundleTest I (F →L[ℝ] ℝ) (localCoefficients (I := I) (V := V) (U := U)) := by
  let q : C(nestedOpen U D, U) := ⟨nestedBaseDiffeomorph (I := I) h,
    (nestedBaseDiffeomorph (I := I) h).continuous⟩
  exact (openDensityHomCLE (I := I) (F := F) (V := V) (U := U)).symm.toContinuousLinearMap.comp
    (TauCeti.BundleTest.localizeCLM (I := I) (F := F →L[ℝ] ℝ)
      (V := ambientCoefficients (I := I) (V := V))
      (iteratedIntrinsicTestExtensionCLM (I := I) (F := F) (V := V) D) q
      (fun s ↦ (tsupport_iteratedIntrinsicTestExtensionCLM h s).le))

private theorem testExtensionCLM_nested_aux {D : Opens M} (h : U ≤ D) :
    (testExtensionCLM (I := I) (F := F) (V := V) (U := U)).comp
      (intrinsicNestedTestComparisonCLM (I := I) (F := F) (V := V) h) =
      iteratedIntrinsicTestExtensionCLM (I := I) (F := F) (V := V) D := by
  let q : C(nestedOpen U D, U) := ⟨nestedBaseDiffeomorph (I := I) h,
    (nestedBaseDiffeomorph (I := I) h).continuous⟩
  apply ContinuousLinearMap.ext
  intro s
  change TauCeti.BundleTest.extendByZeroCLM (I := I) (F := F →L[ℝ] ℝ)
      (V := ambientCoefficients (I := I) (V := V)) (U := U)
      (openDensityHomCLE (I := I) (F := F) (V := V)
        ((openDensityHomCLE (I := I) (F := F) (V := V)).symm
          (TauCeti.BundleTest.localizeCLM (I := I) (F := F →L[ℝ] ℝ)
            (V := ambientCoefficients (I := I) (V := V))
            (iteratedIntrinsicTestExtensionCLM (I := I) (F := F) (V := V) D) q
            (fun t ↦ (tsupport_iteratedIntrinsicTestExtensionCLM h t).le) s))) = _
  erw [ContinuousLinearEquiv.apply_symm_apply]
  exact TauCeti.BundleTest.extendByZeroCLM_localizeCLM _ q
    (fun t ↦ (tsupport_iteratedIntrinsicTestExtensionCLM h t).le) s

private theorem intrinsicNestedTestComparisonCLM_apply {D : Opens M} (h : U ≤ D)
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) (doubleCoefficients (I := I) (V := V) (U := U) D))
    (x : nestedOpen U D) :
    intrinsicNestedTestComparisonCLM (I := I) (F := F) (V := V) h s
      (nestedBaseDiffeomorph (I := I) h x) =
    (TauCeti.DensityBundle.openHomEquiv (I := I) (V := V) (nestedBaseDiffeomorph (I := I) h x)).symm
      (TauCeti.DensityBundle.openHomEquiv (I := I) (V := V) x.val
        (TauCeti.DensityBundle.openHomEquiv (I := I) (M := D)
          (V := (openInclusion (U := D)) *ᵖ V) x (s x))) := by
  unfold intrinsicNestedTestComparisonCLM
  erw [ContinuousLinearMap.comp_apply, openDensityHomCLE_symm_apply,
    TauCeti.BundleTest.localizeCLM_apply]
  congr 1
  change testExtensionCLM (I := I) (F := F) (V := V) (U := D)
    (testExtensionCLM (I := I) (F := F) (M := D)
      (V := (openInclusion (U := D)) *ᵖ V) (U := nestedOpen U D) s) (x.val : M) = _
  erw [testExtensionCLM_apply_of_mem _ x.val,
    testExtensionCLM_apply_of_mem s x]

private theorem tsupport_intrinsicInclusionCLM {D : Opens M} (h : U ≤ D)
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) (localCoefficients (I := I) (V := V) (U := U))) :
    closure {x : D | intrinsicInclusionCLM (I := I) (F := F) (V := V) h s x ≠ 0} =
      (Opens.inclusion h) '' closure {x : U | s x ≠ 0} := by
  let t := inclusionCLM (I := I) (F := F →L[ℝ] ℝ)
    (V := ambientCoefficients (I := I) (V := V)) h
    (openDensityHomCLE (I := I) (F := F) (V := V) s)
  have hset : {x : D | intrinsicInclusionCLM (I := I) (F := F) (V := V) h s x ≠ 0} =
      {x : D | t x ≠ 0} := by
    ext x
    change ((openDensityHomCLE (I := I) (F := F) (V := V) (U := D)).symm t x ≠ 0) ↔
      (t x ≠ 0)
    erw [openDensityHomCLE_symm_apply (I := I) (F := F) (V := V) (U := D)]
    exact not_congr (TauCeti.DensityBundle.openHomEquiv (I := I) (V := V) x).symm.map_eq_zero_iff
  rw [hset]
  obtain ⟨z, hz⟩ := (ofCompactlySupported I (F →L[ℝ] ℝ)
    (pulledAmbientCoefficients (I := I) (V := V) (U := U))).surjective
    (openDensityHomCLE (I := I) (F := F) (V := V) s)
  change closure {x : D | inclusionCLM (I := I) (F := F →L[ℝ] ℝ)
    (V := ambientCoefficients (I := I) (V := V)) h
    (openDensityHomCLE (I := I) (F := F) (V := V) s) x ≠ 0} = _
  rw [← hz, inclusionCLM_ofCompactlySupported]
  erw [LinearEquiv.symm_apply_apply]
  erw [← ContMDiffSection.tsupport_def]
  erw [ContMDiffSection.tsupport_extendByZeroToOpenLinearMap]
  congr 2
  rw [ContMDiffSection.tsupport_def]
  congr 1
  ext x
  change (z.val x ≠ 0) ↔ (s x ≠ 0)
  have hx := congrArg (fun w : TauCeti.BundleTest I (F →L[ℝ] ℝ)
    (pulledAmbientCoefficients (I := I) (V := V) (U := U)) ↦ w x) hz
  change z.val x = openDensityHomCLE (I := I) (F := F) (V := V) s x at hx
  rw [hx]
  erw [openDensityHomCLE_apply]
  exact not_congr (TauCeti.DensityBundle.openHomEquiv (I := I) (V := V) x).map_eq_zero_iff

private def intrinsicNestedTestInverseCLM {D : Opens M} (h : U ≤ D) :
    TauCeti.BundleTest I (F →L[ℝ] ℝ) (localCoefficients (I := I) (V := V) (U := U)) →L[ℝ]
      TauCeti.BundleTest I (F →L[ℝ] ℝ) (doubleCoefficients (I := I) (V := V) (U := U) D) := by
  let VD := (openInclusion (U := D)) *ᵖ V
  let ND := nestedOpen U D
  let q : C(U, ND) := ⟨(nestedBaseDiffeomorph (I := I) h).symm,
    (nestedBaseDiffeomorph (I := I) h).symm.continuous⟩
  have hs : ∀ s : TauCeti.BundleTest I (F →L[ℝ] ℝ)
      (localCoefficients (I := I) (V := V) (U := U)),
      closure {x : D | intrinsicInclusionCLM (I := I) (F := F) (V := V) h s x ≠ 0} ⊆
        Subtype.val '' q '' closure {x : U | s x ≠ 0} := by
    intro s
    rw [tsupport_intrinsicInclusionCLM]
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨q u, ⟨u, hu, rfl⟩, rfl⟩
  exact (openDensityHomCLE (I := I) (F := F) (M := D) (V := VD) (U :=
    ND)).symm.toContinuousLinearMap.comp
    (TauCeti.BundleTest.localizeCLM (I := I) (F := F →L[ℝ] ℝ) (M := D)
      (V := ambientCoefficients (I := I) (M := D) (V := VD))
      (intrinsicInclusionCLM (I := I) (F := F) (V := V) h) q hs)

private theorem intrinsicInclusionCLM_apply {D : Opens M} (h : U ≤ D)
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) (localCoefficients (I := I) (V := V) (U := U)))
    (u : U) : intrinsicInclusionCLM (I := I) (F := F) (V := V) h s (Opens.inclusion h u) =
      (TauCeti.DensityBundle.openHomEquiv (I := I) (V := V) (Opens.inclusion h u)).symm
        (TauCeti.DensityBundle.openHomEquiv (I := I) (V := V) u (s u)) := by
  change (openDensityHomCLE (I := I) (F := F) (V := V) (U := D)).symm
    (inclusionCLM (I := I) (F := F →L[ℝ] ℝ)
      (V := ambientCoefficients (I := I) (V := V)) h
      (openDensityHomCLE (I := I) (F := F) (V := V) s)) (Opens.inclusion h u) = _
  erw [openDensityHomCLE_symm_apply (I := I) (F := F) (V := V) (U := D)]
  congr 1
  erw [inclusionCLM_apply_of_mem, openDensityHomCLE_apply]
  exact Pullback.lift_snd _ _

private theorem intrinsicNestedTestInverseCLM_apply {D : Opens M} (h : U ≤ D)
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) (localCoefficients (I := I) (V := V) (U := U)))
    (x : nestedOpen U D) : intrinsicNestedTestInverseCLM (I := I) (F := F) (V := V) h s x =
      (TauCeti.DensityBundle.openHomEquiv (I := I) (M := D)
        (V := (openInclusion (U := D)) *ᵖ V) x).symm
        ((TauCeti.DensityBundle.openHomEquiv (I := I) (V := V) x.val).symm
          (TauCeti.DensityBundle.openHomEquiv (I := I) (V := V) (nestedBaseDiffeomorph (I := I) h x)
            (s (nestedBaseDiffeomorph (I := I) h x)))) := by
  unfold intrinsicNestedTestInverseCLM
  erw [ContinuousLinearMap.comp_apply, openDensityHomCLE_symm_apply,
    TauCeti.BundleTest.localizeCLM_apply]
  have hi := intrinsicInclusionCLM_apply (I := I) (F := F) (V := V) h s
    (nestedBaseDiffeomorph (I := I) h x)
  exact congrArg (TauCeti.DensityBundle.openHomEquiv (I := I) (M := D)
    (V := (openInclusion (U := D)) *ᵖ V) x).symm hi

private theorem intrinsicNestedTestComparison_left_inv {D : Opens M} (h : U ≤ D)
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) (doubleCoefficients (I := I) (V := V) (U := U) D)) :
    intrinsicNestedTestInverseCLM (I := I) (F := F) (V := V) h
      (intrinsicNestedTestComparisonCLM (I := I) (F := F) (V := V) h s) = s := by
  apply TauCeti.BundleTest.ext
  intro x
  erw [intrinsicNestedTestInverseCLM_apply (I := I) (F := F) (V := V) h _ x,
    intrinsicNestedTestComparisonCLM_apply (I := I) (F := F) (V := V) h s x]
  erw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply,
    ContinuousLinearEquiv.symm_apply_apply]

private theorem intrinsicNestedTestComparison_right_inv {D : Opens M} (h : U ≤ D)
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) (localCoefficients (I := I) (V := V) (U := U))) :
    intrinsicNestedTestComparisonCLM (I := I) (F := F) (V := V) h
      (intrinsicNestedTestInverseCLM (I := I) (F := F) (V := V) h s) = s := by
  apply TauCeti.BundleTest.ext
  intro u
  let x := (nestedBaseDiffeomorph (I := I) h).symm u
  change intrinsicNestedTestComparisonCLM (I := I) (F := F) (V := V) h
    (intrinsicNestedTestInverseCLM (I := I) (F := F) (V := V) h s)
    (nestedBaseDiffeomorph (I := I) h x) = s u
  erw [intrinsicNestedTestComparisonCLM_apply (I := I) (F := F) (V := V) h _ x,
    intrinsicNestedTestInverseCLM_apply (I := I) (F := F) (V := V) h s x]
  erw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.symm_apply_apply]
  dsimp only [x]
  rfl

/-- Identify the intrinsic tests on the actual double pullback with direct intrinsic tests
through native extension, localization, and the tangent-density comparisons. -/
def nestedTestCLE {D : Opens M} (h : U ≤ D) :
    TauCeti.BundleTest I (F →L[ℝ] ℝ) ((fun x : (Opens.comap (⟨Subtype.val, continuous_subtypeVal⟩
      : C(D, M)) U) ↦ ((⟨Subtype.val, continuous_subtypeVal⟩ : C((Opens.comap (⟨Subtype.val,
      continuous_subtypeVal⟩ : C(D, M)) U), D)) *ᵖ ((⟨Subtype.val, continuous_subtypeVal⟩ : C(D,
      M)) *ᵖ V)) x →L[ℝ] TauCeti.DensityBundle I (Opens.comap (⟨Subtype.val,
      continuous_subtypeVal⟩ : C(D, M)) U) x)) ≃L[ℝ]
      TauCeti.BundleTest I (F →L[ℝ] ℝ) ((fun x : U ↦ ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U,
        M)) *ᵖ V) x →L[ℝ] TauCeti.DensityBundle I U x)) :=
  ContinuousLinearEquiv.ofContinuousLinearMap
    (intrinsicNestedTestComparisonCLM (I := I) (F := F) (V := V) h)
    (intrinsicNestedTestInverseCLM (I := I) (F := F) (V := V) h)
    (by apply ContinuousLinearMap.ext; intro s; exact intrinsicNestedTestComparison_right_inv h s)
    (by apply ContinuousLinearMap.ext; intro s; exact intrinsicNestedTestComparison_left_inv h s)

/-- The nested comparison preserves each underlying fibrewise functional. -/
theorem nestedTestCLE_apply {D : Opens M} (h : U ≤ D) :
    let cD : C(D, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    let N := Opens.comap cD U
    let cN : C(N, D) := ⟨Subtype.val, continuous_subtypeVal⟩
    ∀ (s : TauCeti.BundleTest I (F →L[ℝ] ℝ)
      (fun x : N ↦ (cN *ᵖ (cD *ᵖ V)) x →L[ℝ] TauCeti.DensityBundle I N x)) (x : N),
      nestedTestCLE (I := I) (F := F) (V := V) h s
        (⟨x.val.val, x.property⟩ : U) = s x := by
  intro cD N cN s x
  change intrinsicNestedTestComparisonCLM (I := I) (F := F) (V := V) h s _ = _
  erw [intrinsicNestedTestComparisonCLM_apply (I := I) (F := F) (V := V) h s x]
  erw [TauCeti.DensityBundle.openHomEquiv_apply (I := I) (M := D) (V := cD *ᵖ V),
    TauCeti.DensityBundle.openHomEquiv_apply (I := I) (V := V),
    TauCeti.DensityBundle.openHomEquiv_symm_apply (I := I) (V := V)]

/-- The inverse nested comparison evaluates at the canonical nested-base identification. -/
theorem nestedTestCLE_symm_apply {D : Opens M} (h : U ≤ D) :
    let cD : C(D, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    let N := Opens.comap cD U
    ∀ (s : TauCeti.BundleTest I (F →L[ℝ] ℝ)
      (fun x : U ↦ ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V) x →L[ℝ]
        TauCeti.DensityBundle I U x)) (x : N),
      (nestedTestCLE (I := I) (F := F) (V := V) h).symm s x =
        s (⟨x.val.val, x.property⟩ : U) := by
  intro cD N s x
  change intrinsicNestedTestInverseCLM (I := I) (F := F) (V := V) h s x = _
  erw [intrinsicNestedTestInverseCLM_apply (I := I) (F := F) (V := V) h s x]
  erw [TauCeti.DensityBundle.openHomEquiv_apply (I := I) (V := V),
    TauCeti.DensityBundle.openHomEquiv_symm_apply (I := I) (V := V),
    TauCeti.DensityBundle.openHomEquiv_symm_apply (I := I) (M := D) (V := cD *ᵖ V)]
  rfl

/-- Actual direct and successive intrinsic test extensions agree through the comparison. -/
theorem testExtensionCLM_nested {D : Opens M} (h : U ≤ D) :
    let cD : C(D, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    let N := Opens.comap cD U
    (testExtensionCLM (I := I) (F := F) (V := V) (U := U)).comp
      (nestedTestCLE (I := I) (F := F) (V := V) h).toContinuousLinearMap =
    (testExtensionCLM (I := I) (F := F) (V := V) (U := D)).comp
      (testExtensionCLM (I := I) (F := F) (M := D) (V := cD *ᵖ V) (U := N)) := by
  intro cD _
  exact testExtensionCLM_nested_aux (I := I) (F := F) (V := V) h

/-- The compact-convergence transpose of the actual double-pullback test comparison. -/
def nestedComparisonCLM {D : Opens M} (h : U ≤ D) :
    TauCeti.BundleDistribution I U F (((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M))) *ᵖ V) →L[ℝ]
      TauCeti.BundleDistribution I ((Opens.comap (⟨Subtype.val, continuous_subtypeVal⟩ : C(D, M))
        U)) F
        (((⟨Subtype.val, continuous_subtypeVal⟩ : C((Opens.comap (⟨Subtype.val,
          continuous_subtypeVal⟩ : C(D, M)) U), D))) *ᵖ
          (((⟨Subtype.val, continuous_subtypeVal⟩ : C(D, M))) *ᵖ V)) :=
  (nestedTestCLE (I := I) (F := F) (V := V) h).toContinuousLinearMap.precompCompactConvergenceCLM ℝ

/-- Direct intrinsic restriction agrees with successive independently instantiated intrinsic
restrictions through the actual double-pullback comparison. -/
theorem restrictCLM_nested {D : Opens M} (h : U ≤ D)
    (T : TauCeti.BundleDistribution I M F V) :
    nestedComparisonCLM (I := I) (F := F) (V := V) h
      (restrictCLM (I := I) (F := F) (V := V) (U := U) T) =
    restrictCLM (I := I) (F := F) (M := D)
      (V := ((⟨Subtype.val, continuous_subtypeVal⟩ : C(D, M))) *ᵖ V) (U := (Opens.comap
        (⟨Subtype.val, continuous_subtypeVal⟩ : C(D, M)) U))
      (restrictCLM (I := I) (F := F) (V := V) (U := D) T) := by
  apply ContinuousLinearMap.ext
  intro s
  change T (testExtensionCLM (I := I) (F := F) (V := V) (U := U)
      (intrinsicNestedTestComparisonCLM (I := I) (F := F) (V := V) h s)) =
    T (iteratedIntrinsicTestExtensionCLM (I := I) (F := F) (V := V) D s)
  exact congrArg T (congrArg (fun L ↦ L s)
    (testExtensionCLM_nested_aux (I := I) (F := F) (V := V) h))

/-- Intrinsic tests on the universal open subset identify with ambient tests. -/
def univTestCLE :
    let c : C((⊤ : Opens M), M) := ⟨Subtype.val, continuous_subtypeVal⟩
    TauCeti.BundleTest I (F →L[ℝ] ℝ)
      (fun x : (⊤ : Opens M) ↦ (c *ᵖ V) x →L[ℝ] TauCeti.DensityBundle I (⊤ : Opens M) x) ≃L[ℝ]
    TauCeti.BundleTest I (F →L[ℝ] ℝ) (fun x ↦ V x →L[ℝ] TauCeti.DensityBundle I M x) := by
  intro _
  exact (openDensityHomCLE (I := I) (F := F) (V := V) (U := ⊤)).trans
    (TauCeti.BundleTest.univCLE (I := I) (F := F →L[ℝ] ℝ)
      (V := ambientCoefficients (I := I) (V := V)))

/-- Restriction to the universal open subset is a compact-convergence equivalence. -/
def univCLE :
    let c : C((⊤ : Opens M), M) := ⟨Subtype.val, continuous_subtypeVal⟩
    TauCeti.BundleDistribution I M F V ≃L[ℝ]
      TauCeti.BundleDistribution I (⊤ : Opens M) F (c *ᵖ V) := by
  intro c
  let e := univTestCLE (I := I) (F := F) (V := V)
  refine ContinuousLinearEquiv.ofContinuousLinearMap
    (e.toContinuousLinearMap.precompCompactConvergenceCLM ℝ)
    (e.symm.toContinuousLinearMap.precompCompactConvergenceCLM ℝ) ?_ ?_
  · apply ContinuousLinearMap.ext
    intro T
    apply ContinuousLinearMap.ext
    intro s
    change T (e.symm (e s)) = T s
    exact congrArg T (e.symm_apply_apply s)
  · apply ContinuousLinearMap.ext
    intro T
    apply ContinuousLinearMap.ext
    intro s
    change T (e (e.symm s)) = T s
    exact congrArg T (e.apply_symm_apply s)

/-- The universal-open equivalence has the actual intrinsic restriction as its forward map. -/
theorem univCLE_toContinuousLinearMap :
    (univCLE (I := I) (F := F) (V := V)).toContinuousLinearMap =
      restrictCLM (I := I) (F := F) (V := V) (U := ⊤) := by
  apply ContinuousLinearMap.ext
  intro T
  apply ContinuousLinearMap.ext
  intro s
  change T ((TauCeti.BundleTest.univCLE (I := I) (F := F →L[ℝ] ℝ)
    (V := ambientCoefficients (I := I) (V := V)))
      (openDensityHomCLE (I := I) (F := F) (V := V) s)) =
    T (testExtensionCLM (I := I) (F := F) (V := V) s)
  have h := congrArg (fun L ↦ L (openDensityHomCLE (I := I) (F := F) (V := V) s))
    (TauCeti.BundleTest.univCLE_toContinuousLinearMap (I := I) (F := F →L[ℝ] ℝ)
      (V := ambientCoefficients (I := I) (V := V)))
  exact congrArg T h

end TauCeti.BundleDistribution
