/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.ExtendByZero.Topology
public import TauCeti.Geometry.Manifold.VectorBundle.Density.OpenSubset
public import TauCeti.Geometry.Manifold.Diffeomorph.Subtype

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
open TauCeti.DensityBundle (localCoefficients ambientCoefficients pulledAmbientCoefficients)

namespace TauCeti.BundleTest


section Density
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {U : Opens M}

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]

private abbrev intrinsicFrame (x : U) :=
  trivializationAt (F →L[ℝ] ℝ) (localCoefficients (I := I) (V := V) (U := U)) x
private abbrev pulledFrame (x : U) :=
  (trivializationAt (F →L[ℝ] ℝ) (ambientCoefficients (I := I) (V := V)) (x : M)).pullback
    ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)))

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
  simpa only [pulledFrame, Trivialization.pullback_baseSet, ContinuousMap.coe_mk,
    Set.mem_preimage] using
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
  -- Public coordinate evaluation has reduced the pulled frame to the ambient Hom frame.
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
  -- Use the same intrinsic frame after evaluating the inverse coefficient map.
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
    let e := (trivializationAt (F →L[ℝ] ℝ) (localCoefficients (I := I) (V := V) (U := U)))
    let e' := (trivializationAt (F →L[ℝ] ℝ) ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ
      (ambientCoefficients (I := I) (V := V))))
    let := frameTopology (I := I) (n := ∞) e
      (fun x ↦ ⟨(e x).baseSet, (e x).open_baseSet⟩) (fun _ ↦ subset_rfl)
    let := frameTopology (I := I) (n := ∞) e'
      (fun x ↦ ⟨(e' x).baseSet, (e' x).open_baseSet⟩) (fun _ ↦ subset_rfl)
    supportedIn I (F →L[ℝ] ℝ) ∞ ((localCoefficients (I := I) (V := V) (U := U))) K ≃L[ℝ]
      supportedIn I (F →L[ℝ] ℝ) ∞ (((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ
    (ambientCoefficients (I := I) (V := V)))) K := by
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

/-- The fixed-support comparison evaluates by the pointwise density comparison. -/
@[simp]
theorem openDensityHomSupportedInCLE_apply (K : Set U)
    (s : supportedIn I (F →L[ℝ] ℝ) ∞ (localCoefficients (I := I) (V := V) (U := U)) K)
    (x : U) :
    dsimp% only [ContinuousMap.coe_mk] (
    (openDensityHomSupportedInCLE (I := I) (F := F) (V := V) K s).val x =
      TauCeti.DensityBundle.openHomEquiv x (s.val x)) := by
  erw [coe_mapSupportedInEquiv, mapEquiv_apply]
  rfl

/-- The inverse fixed-support comparison evaluates by the inverse density comparison. -/
@[simp]
theorem openDensityHomSupportedInCLE_symm_apply (K : Set U) :
    let e := trivializationAt (F →L[ℝ] ℝ)
      (localCoefficients (I := I) (V := V) (U := U))
    let e' := trivializationAt (F →L[ℝ] ℝ)
      (pulledAmbientCoefficients (I := I) (V := V) (U := U))
    let := frameTopology (I := I) (n := ∞) e
      (fun x ↦ ⟨(e x).baseSet, (e x).open_baseSet⟩) (fun _ ↦ subset_rfl)
    let := frameTopology (I := I) (n := ∞) e'
      (fun x ↦ ⟨(e' x).baseSet, (e' x).open_baseSet⟩) (fun _ ↦ subset_rfl)
    ∀ (s : supportedIn I (F →L[ℝ] ℝ) ∞
      (pulledAmbientCoefficients (I := I) (V := V) (U := U)) K) (x : U),
      dsimp% only [ContinuousMap.coe_mk] (
      ((openDensityHomSupportedInCLE (I := I) (F := F) (V := V) K).symm s).val x =
        (TauCeti.DensityBundle.openHomEquiv x).symm (s.val x)) := by
  intro e e' _ _ s x
  erw [coe_mapSupportedInEquiv_symm, mapEquiv_symm, mapEquiv_apply]
  rfl

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
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) ((localCoefficients (I := I) (V := V) (U := U))))
    (x : U) : densityTestLinearEquiv (I := I) (F := F) (V := V) s x =
      TauCeti.DensityBundle.openHomEquiv x (s x) := by
  -- The native test equivalence wraps this same algebraic compact-support transport.
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
      (ambientCoefficients (I := I) (V := V)))))
    (x : U) : (densityTestLinearEquiv (I := I) (F := F) (V := V)).symm s x =
      (TauCeti.DensityBundle.openHomEquiv x).symm (s x) := by
  -- Read the inverse native test equivalence through its algebraic section transport.
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
    TauCeti.BundleTest I (F →L[ℝ] ℝ) ((localCoefficients (I := I) (V := V) (U := U))) ≃L[ℝ]
      TauCeti.BundleTest I (F →L[ℝ] ℝ) (((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ
    (ambientCoefficients (I := I) (V := V)))) := by
  let e := intrinsicFrame (I := I) (F := F) (V := V) (U := U)
  let e' := trivializationAt (F →L[ℝ] ℝ)
    (pulledAmbientCoefficients (I := I) (V := V) (U := U))
  letI := frameTopology (I := I) (n := ∞) e
    (fun x ↦ ⟨(e x).baseSet, (e x).open_baseSet⟩) (fun _ ↦ subset_rfl)
  letI := frameTopology (I := I) (n := ∞) e'
    (fun x ↦ ⟨(e' x).baseSet, (e' x).open_baseSet⟩) (fun _ ↦ subset_rfl)
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
    exact (openDensityHomSupportedInCLE_apply (I := I) (F := F) (V := V) K z x).symm
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
    exact (openDensityHomSupportedInCLE_symm_apply (I := I) (F := F) (V := V) K z x).symm

omit [T2Space M] in
/-- The intrinsic test comparison evaluates by the native pointwise open-density map. -/
@[simp]
theorem openDensityHomCLE_apply
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) ((localCoefficients (I := I) (V := V) (U := U))))
    (x : U) :
    dsimp% only [ContinuousMap.coe_mk] (
    openDensityHomCLE (I := I) (F := F) (V := V) s x =
      TauCeti.DensityBundle.openHomEquiv x (s x)) := by
  exact densityTestLinearEquiv_apply s x

omit [T2Space M] in
/-- The inverse intrinsic test comparison evaluates by the inverse native density map. -/
@[simp]
theorem openDensityHomCLE_symm_apply
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) (((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ
      (ambientCoefficients (I := I) (V := V)))))
    (x : U) :
    dsimp% only [ContinuousMap.coe_mk] (
    (openDensityHomCLE (I := I) (F := F) (V := V)).symm s x =
      (TauCeti.DensityBundle.openHomEquiv x).symm (s x)) := by
  exact densityTestLinearEquiv_symm_apply s x

omit [T2Space M] in
/-- The intrinsic density comparison commutes with multiplication by smooth real functions. -/
theorem openDensityHomCLE_smulLeftCLM (f : C^∞⟮I, U; ℝ⟯)
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) ((localCoefficients (I := I) (V := V) (U := U)))) :
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
    TauCeti.BundleTest I (F →L[ℝ] ℝ) ((localCoefficients (I := I) (V := V) (U := U))) →L[ℝ]
      TauCeti.BundleTest I (F →L[ℝ] ℝ) ((ambientCoefficients (I := I) (V := V))) := by
  exact (TauCeti.BundleTest.extendByZeroCLM (I := I) (F := F →L[ℝ] ℝ)
    (V := ambientCoefficients (I := I) (V := V)) (U := U)).comp
    (openDensityHomCLE (I := I) (F := F) (V := V) (U := U)).toContinuousLinearMap

/-- Intrinsic test extension is native extension after the open density comparison. -/
theorem testExtensionCLM_apply
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) ((localCoefficients (I := I) (V := V) (U := U)))) :
    testExtensionCLM (I := I) (F := F) (V := V) s =
      TauCeti.BundleTest.extendByZeroCLM (I := I) (F := F →L[ℝ] ℝ)
        (V := ambientCoefficients (I := I) (V := V)) (U := U)
        (openDensityHomCLE (I := I) (F := F) (V := V) s) :=
  (rfl)

/-- On the open subset, intrinsic extension evaluates by the native density comparison. -/
@[simp]
theorem testExtensionCLM_apply_of_mem
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) ((localCoefficients (I := I) (V := V) (U := U))))
    (x : U) :
    dsimp% only [ContinuousMap.coe_mk] (
    testExtensionCLM (I := I) (F := F) (V := V) s (x : M) =
      TauCeti.DensityBundle.openHomEquiv x (s x)) := by
  rw [testExtensionCLM_apply]
  erw [TauCeti.BundleTest.extendByZeroCLM_apply_of_mem]
  exact openDensityHomCLE_apply s x

/-- Intrinsic test extension vanishes outside the open subset. -/
@[simp]
theorem testExtensionCLM_apply_of_notMem
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) ((localCoefficients (I := I) (V := V) (U := U))))
    {x : M} (hx : x ∉ U) :
    testExtensionCLM (I := I) (F := F) (V := V) s x = 0 := by
  rw [testExtensionCLM_apply]
  exact TauCeti.BundleTest.extendByZeroCLM_apply_of_notMem (I := I) (F := F →L[ℝ] ℝ)
    (V := ambientCoefficients (I := I) (V := V))
    (openDensityHomCLE (I := I) (F := F) (V := V) s) hx

/-- Restriction of native bundle distributions, obtained by compact-convergence transpose
of intrinsic dual-density test extension. -/
def restrictCLM :
    let c : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    TauCeti.BundleDistribution I M F V →L[ℝ] TauCeti.BundleDistribution I U F (c *ᵖ V) := by
  dsimp only
  exact ((openDensityHomCLE (I := I) (F := F) (V := V)
    (U := U)).toContinuousLinearMap.precompCompactConvergenceCLM ℝ).comp
      (restrictDualCLM (I := I) (F := F →L[ℝ] ℝ)
        (V := ambientCoefficients (I := I) (V := V)) (W := ℝ) (U := U))

/-- Restriction pairs with an intrinsic test by pairing with its ambient extension. -/
@[simp]
theorem restrictCLM_apply :
    dsimp% only [ContinuousMap.coe_mk] (
    ∀ (T : TauCeti.BundleDistribution I M F V)
      (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) ((localCoefficients (I := I) (V := V) (U := U)))),
      restrictCLM (I := I) (F := F) (V := V) T s =
        T (testExtensionCLM (I := I) (F := F) (V := V) s)) := by
  intro T s
  -- The composed transpose is evaluated at the same canonical open-test carrier.
  change restrictDualCLM (I := I) (F := F →L[ℝ] ℝ)
    (V := ambientCoefficients (I := I) (V := V)) (W := ℝ) (U := U) T
      (openDensityHomCLE (I := I) (F := F) (V := V) s) = _
  erw [restrictDualCLM_apply]
  rfl

/-- A point mass inside the open subset restricts by transposing the native density map. -/
theorem restrictCLM_delta_of_mem :
    ∀ (x : U) (ℓ : (ambientCoefficients (I := I) (V := V)) (x : M) →L[ℝ] ℝ),
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
    ∀ (x : M) (_hx : x ∉ U) (ℓ : (ambientCoefficients (I := I) (V := V)) x →L[ℝ] ℝ),
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
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) ((localCoefficients (I := I) (V := V) (U := U)))) :
    closure {x : M | testExtensionCLM (I := I) (F := F) (V := V) s x ≠ 0} =
      Subtype.val '' closure {x : U | s x ≠ 0} := by
  simp only [testExtensionCLM_apply]
  trans Subtype.val '' closure {x : U | openDensityHomCLE (I := I) (F := F) (V := V) s x ≠ 0}
  · exact TauCeti.BundleTest.tsupport_extendByZeroCLM (I := I) (F := F →L[ℝ] ℝ)
      (V := ambientCoefficients (I := I) (V := V)) (U := U)
      (openDensityHomCLE (I := I) (F := F) (V := V) s)
  · congr 2
    ext x
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq]
    erw [openDensityHomCLE_apply]
    exact not_congr (TauCeti.DensityBundle.openHomEquiv (I := I) (V := V) x).map_eq_zero_iff

/-- Intrinsic test extension commutes with the restriction of a smooth ambient multiplier. -/
theorem testExtensionCLM_smulLeftCLM (f : C^∞⟮I, M; ℝ⟯)
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) ((localCoefficients (I := I) (V := V) (U := U)))) :
    testExtensionCLM (I := I) (F := F) (V := V) (TauCeti.BundleTest.smulLeftCLM (f.restrict U) s) =
      TauCeti.BundleTest.smulLeftCLM f (testExtensionCLM (I := I) (F := F) (V := V) s) := by
  rw [testExtensionCLM_apply, testExtensionCLM_apply, openDensityHomCLE_smulLeftCLM]
  exact TauCeti.BundleTest.extendByZeroCLM_smulLeftCLM f _

/-- Native distribution restriction commutes with smooth real multiplication. -/
theorem restrictCLM_smulLeftDualCLM :
    ∀ (f : C^∞⟮I, M; ℝ⟯) (T : TauCeti.BundleDistribution I M F V),
      restrictCLM (I := I) (F := F) (V := V) (U := U)
        (TauCeti.BundleTest.smulLeftDualCLM (I := I) (F := F →L[ℝ] ℝ)
          (V := (ambientCoefficients (I := I) (V := V))) f T) =
      TauCeti.BundleTest.smulLeftDualCLM (I := I) (F := F →L[ℝ] ℝ)
        (V := (localCoefficients (I := I) (V := V) (U := U))) (f.restrict U)
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

private theorem intrinsicInclusionCLM_eq {D : Opens M} (h : U ≤ D)
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) (localCoefficients (I := I) (V := V) (U := U))) :
    intrinsicInclusionCLM (I := I) (F := F) (V := V) h s =
      (openDensityHomCLE (I := I) (F := F) (V := V) (U := D)).symm
        (inclusionCLM (I := I) (F := F →L[ℝ] ℝ)
          (V := ambientCoefficients (I := I) (V := V)) h
          (openDensityHomCLE (I := I) (F := F) (V := V) s)) :=
  rfl

private abbrev nestedOpen (U D : Opens M) : Opens D :=
  Opens.comap (⟨Subtype.val, continuous_subtypeVal⟩ : C(D, M)) U

private abbrev doubleCoefficients (D : Opens M) :=
  localCoefficients (I := I) (V := (⟨Subtype.val, continuous_subtypeVal⟩ : C(D, M)) *ᵖ V)
    (U := nestedOpen U D)

private def iteratedIntrinsicTestExtensionCLM (D : Opens M) :
    TauCeti.BundleTest I (F →L[ℝ] ℝ) (doubleCoefficients (I := I) (V := V) (U := U) D) →L[ℝ]
      TauCeti.BundleTest I (F →L[ℝ] ℝ) (ambientCoefficients (I := I) (V := V)) :=
  (testExtensionCLM (I := I) (F := F) (V := V) (U := D)).comp
    (testExtensionCLM (I := I) (F := F) (M := D)
      (V := (⟨Subtype.val, continuous_subtypeVal⟩ : C(D, M)) *ᵖ V) (U := nestedOpen U D))

private theorem iteratedIntrinsicTestExtensionCLM_apply (D : Opens M)
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) (doubleCoefficients (I := I) (V := V) (U := U) D)) :
    iteratedIntrinsicTestExtensionCLM (I := I) (F := F) (V := V) D s =
      testExtensionCLM (I := I) (F := F) (V := V) (U := D)
        (testExtensionCLM (I := I) (F := F) (M := D)
          (V := (⟨Subtype.val, continuous_subtypeVal⟩ : C(D, M)) *ᵖ V) (U := nestedOpen U D) s) :=
  rfl

private theorem tsupport_iteratedIntrinsicTestExtensionCLM {D : Opens M} (h : U ≤ D)
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) (doubleCoefficients (I := I) (V := V) (U := U) D)) :
    closure {x : M | iteratedIntrinsicTestExtensionCLM (I := I) (F := F) (V := V) D s x ≠ 0} =
      Subtype.val '' (Diffeomorph.nestedOpen (I := I) (n := ∞) h) ''
        closure {x : nestedOpen U D | s x ≠ 0}
        := by
  simp only [iteratedIntrinsicTestExtensionCLM_apply]
  erw [tsupport_testExtensionCLM (I := I) (F := F) (V := V) (U := D)]
  erw [tsupport_testExtensionCLM (I := I) (F := F) (M := D)
    (V := (⟨Subtype.val, continuous_subtypeVal⟩ : C(D, M)) *ᵖ V) (U := nestedOpen U D)]
  rw [Set.image_image, Set.image_image]
  simp only [Diffeomorph.nestedOpen_apply_coe]

private def intrinsicNestedTestComparisonCLM {D : Opens M} (h : U ≤ D) :
    TauCeti.BundleTest I (F →L[ℝ] ℝ) (doubleCoefficients (I := I) (V := V) (U := U) D) →L[ℝ]
      TauCeti.BundleTest I (F →L[ℝ] ℝ) (localCoefficients (I := I) (V := V) (U := U)) := by
  let q : C(nestedOpen U D, U) := ⟨Diffeomorph.nestedOpen (I := I) (n := ∞) h,
    (Diffeomorph.nestedOpen (I := I) (n := ∞) h).continuous⟩
  exact (openDensityHomCLE (I := I) (F := F) (V := V) (U := U)).symm.toContinuousLinearMap.comp
    (TauCeti.BundleTest.localizeCLM (I := I) (F := F →L[ℝ] ℝ)
      (V := ambientCoefficients (I := I) (V := V))
      (iteratedIntrinsicTestExtensionCLM (I := I) (F := F) (V := V) D) q
      (fun s ↦ (tsupport_iteratedIntrinsicTestExtensionCLM h s).le))

private theorem testExtensionCLM_nested_aux {D : Opens M} (h : U ≤ D) :
    (testExtensionCLM (I := I) (F := F) (V := V) (U := U)).comp
      (intrinsicNestedTestComparisonCLM (I := I) (F := F) (V := V) h) =
      iteratedIntrinsicTestExtensionCLM (I := I) (F := F) (V := V) D := by
  let q : C(nestedOpen U D, U) := ⟨Diffeomorph.nestedOpen (I := I) (n := ∞) h,
    (Diffeomorph.nestedOpen (I := I) (n := ∞) h).continuous⟩
  apply ContinuousLinearMap.ext
  intro s
  rw [ContinuousLinearMap.comp_apply, testExtensionCLM_apply]
  unfold intrinsicNestedTestComparisonCLM
  erw [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply]
  exact TauCeti.BundleTest.extendByZeroCLM_localizeCLM _ q
    (fun t ↦ (tsupport_iteratedIntrinsicTestExtensionCLM h t).le) s

private theorem intrinsicNestedTestComparisonCLM_apply {D : Opens M} (h : U ≤ D)
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) (doubleCoefficients (I := I) (V := V) (U := U) D))
    (x : nestedOpen U D) :
    intrinsicNestedTestComparisonCLM (I := I) (F := F) (V := V) h s
      (⟨x.val.val, x.property⟩ : U) =
    (TauCeti.DensityBundle.openHomEquiv (I := I) (V := V) (⟨x.val.val, x.property⟩ : U)).symm
      (TauCeti.DensityBundle.openHomEquiv (I := I) (V := V) x.val
        (TauCeti.DensityBundle.openHomEquiv (I := I) (M := D)
          (V := (⟨Subtype.val, continuous_subtypeVal⟩ : C(D, M)) *ᵖ V) x (s x))) := by
  unfold intrinsicNestedTestComparisonCLM
  erw [ContinuousLinearMap.comp_apply, openDensityHomCLE_symm_apply,
    TauCeti.BundleTest.localizeCLM_apply]
  congr 1
  rw [iteratedIntrinsicTestExtensionCLM_apply]
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
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, intrinsicInclusionCLM_eq]
    erw [openDensityHomCLE_symm_apply (I := I) (F := F) (V := V) (U := D)]
    exact not_congr (TauCeti.DensityBundle.openHomEquiv (I := I) (V := V) x).symm.map_eq_zero_iff
  rw [hset, tsupport_inclusionCLM]
  apply congrArg (fun K : Set U ↦ (Opens.inclusion h) '' closure K)
  ext x
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq]
  erw [openDensityHomCLE_apply]
  exact not_congr (TauCeti.DensityBundle.openHomEquiv (I := I) (V := V) x).map_eq_zero_iff

private def intrinsicNestedTestInverseCLM {D : Opens M} (h : U ≤ D) :
    TauCeti.BundleTest I (F →L[ℝ] ℝ) (localCoefficients (I := I) (V := V) (U := U)) →L[ℝ]
      TauCeti.BundleTest I (F →L[ℝ] ℝ) (doubleCoefficients (I := I) (V := V) (U := U) D) := by
  let VD := (⟨Subtype.val, continuous_subtypeVal⟩ : C(D, M)) *ᵖ V
  let ND := nestedOpen U D
  let q : C(U, ND) := ⟨(Diffeomorph.nestedOpen (I := I) (n := ∞) h).symm,
    (Diffeomorph.nestedOpen (I := I) (n := ∞) h).symm.continuous⟩
  have hs : ∀ s : TauCeti.BundleTest I (F →L[ℝ] ℝ)
      (localCoefficients (I := I) (V := V) (U := U)),
      closure {x : D | intrinsicInclusionCLM (I := I) (F := F) (V := V) h s x ≠ 0} ⊆
        Subtype.val '' q '' closure {x : U | s x ≠ 0} := by
    intro s
    rw [tsupport_intrinsicInclusionCLM]
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨q u, ⟨u, hu, rfl⟩, ?_⟩
    exact Diffeomorph.nestedOpen_symm_apply_coe h u
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
  rw [intrinsicInclusionCLM_eq]
  erw [openDensityHomCLE_symm_apply (I := I) (F := F) (V := V) (U := D)]
  congr 1
  erw [inclusionCLM_apply_of_mem, openDensityHomCLE_apply]
  exact Pullback.lift_snd _ _

private theorem intrinsicNestedTestInverseCLM_apply {D : Opens M} (h : U ≤ D)
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) (localCoefficients (I := I) (V := V) (U := U)))
    (x : nestedOpen U D) : intrinsicNestedTestInverseCLM (I := I) (F := F) (V := V) h s x =
      (TauCeti.DensityBundle.openHomEquiv (I := I) (M := D)
        (V := (⟨Subtype.val, continuous_subtypeVal⟩ : C(D, M)) *ᵖ V) x).symm
        ((TauCeti.DensityBundle.openHomEquiv (I := I) (V := V) x.val).symm
          (TauCeti.DensityBundle.openHomEquiv (I := I) (V := V) (⟨x.val.val, x.property⟩ : U)
            (s (⟨x.val.val, x.property⟩ : U)))) := by
  unfold intrinsicNestedTestInverseCLM
  erw [ContinuousLinearMap.comp_apply, openDensityHomCLE_symm_apply,
    TauCeti.BundleTest.localizeCLM_apply]
  have hi := intrinsicInclusionCLM_apply (I := I) (F := F) (V := V) h s
    (⟨x.val.val, x.property⟩ : U)
  exact congrArg (TauCeti.DensityBundle.openHomEquiv (I := I) (M := D)
    (V := (⟨Subtype.val, continuous_subtypeVal⟩ : C(D, M)) *ᵖ V) x).symm hi

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
  -- The public inverse formula fixes the concrete point where the dependent fibre is read.
  let x : nestedOpen U D := ⟨⟨u.val, h u.property⟩, u.property⟩
  -- The CLE packages this already constructed comparison map on the identical test carrier.
  change intrinsicNestedTestComparisonCLM (I := I) (F := F) (V := V) h
    (intrinsicNestedTestInverseCLM (I := I) (F := F) (V := V) h s)
    (⟨x.val.val, x.property⟩ : U) = s u
  erw [intrinsicNestedTestComparisonCLM_apply (I := I) (F := F) (V := V) h _ x,
    intrinsicNestedTestInverseCLM_apply (I := I) (F := F) (V := V) h s x]
  erw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.symm_apply_apply]

/-- Identify the intrinsic tests on the actual double pullback with direct intrinsic tests
through native extension, localization, and the tangent-density comparisons. -/
def nestedTestCLE {D : Opens M} (h : U ≤ D) :
    let cD : C(D, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    let N := Opens.comap cD U
    TauCeti.BundleTest I (F →L[ℝ] ℝ)
      (localCoefficients (I := I) (V := cD *ᵖ V) (U := N)) ≃L[ℝ]
      TauCeti.BundleTest I (F →L[ℝ] ℝ)
        (localCoefficients (I := I) (V := V) (U := U)) := by
  intro cD N
  exact ContinuousLinearEquiv.ofContinuousLinearMap
    (intrinsicNestedTestComparisonCLM (I := I) (F := F) (V := V) h)
    (intrinsicNestedTestInverseCLM (I := I) (F := F) (V := V) h)
    (by apply ContinuousLinearMap.ext; intro s; exact intrinsicNestedTestComparison_right_inv h s)
    (by apply ContinuousLinearMap.ext; intro s; exact intrinsicNestedTestComparison_left_inv h s)

/-- The nested comparison preserves each underlying fibrewise functional. -/
@[simp]
theorem nestedTestCLE_apply {D : Opens M} (h : U ≤ D) :
    dsimp% only [ContinuousMap.coe_mk] (
    let cD : C(D, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    let N := Opens.comap cD U
    ∀ (s : TauCeti.BundleTest I (F →L[ℝ] ℝ)
      (localCoefficients (I := I) (V := cD *ᵖ V) (U := N))) (x : N),
      nestedTestCLE (I := I) (F := F) (V := V) h s
        (⟨x.val.val, x.property⟩ : U) = s x) := by
  let cD : C(D, M) := ⟨Subtype.val, continuous_subtypeVal⟩
  intro s x
  -- The CLE packages this already constructed comparison map on the identical test carrier.
  change intrinsicNestedTestComparisonCLM (I := I) (F := F) (V := V) h s _ = _
  erw [intrinsicNestedTestComparisonCLM_apply (I := I) (F := F) (V := V) h s x]
  erw [TauCeti.DensityBundle.openHomEquiv_apply (I := I) (M := D) (V := cD *ᵖ V),
    TauCeti.DensityBundle.openHomEquiv_apply (I := I) (V := V),
    TauCeti.DensityBundle.openHomEquiv_symm_apply (I := I) (V := V)]
  rfl

/-- The inverse nested comparison evaluates at the canonical nested-base identification. -/
@[simp]
theorem nestedTestCLE_symm_apply {D : Opens M} (h : U ≤ D) :
    dsimp% only [ContinuousMap.coe_mk] (
    let cD : C(D, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    let N := Opens.comap cD U
    ∀ (s : TauCeti.BundleTest I (F →L[ℝ] ℝ)
      (localCoefficients (I := I) (V := V) (U := U))) (x : N),
      (nestedTestCLE (I := I) (F := F) (V := V) h).symm s x =
        s (⟨x.val.val, x.property⟩ : U)) := by
  let cD : C(D, M) := ⟨Subtype.val, continuous_subtypeVal⟩
  intro s x
  -- The inverse CLE packages this map without changing its fibre values.
  change intrinsicNestedTestInverseCLM (I := I) (F := F) (V := V) h s x = _
  erw [intrinsicNestedTestInverseCLM_apply (I := I) (F := F) (V := V) h s x]
  erw [TauCeti.DensityBundle.openHomEquiv_apply (I := I) (V := V),
    TauCeti.DensityBundle.openHomEquiv_symm_apply (I := I) (V := V),
    TauCeti.DensityBundle.openHomEquiv_symm_apply (I := I) (M := D) (V := cD *ᵖ V)]

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
    let cU : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    let cD : C(D, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    let N := Opens.comap cD U
    let cN : C(N, D) := ⟨Subtype.val, continuous_subtypeVal⟩
    TauCeti.BundleDistribution I U F (cU *ᵖ V) →L[ℝ]
      TauCeti.BundleDistribution I N F (cN *ᵖ (cD *ᵖ V)) := by
  intro _ cD N _
  exact (nestedTestCLE (I := I) (F := F) (V := V) h).toContinuousLinearMap
    |>.precompCompactConvergenceCLM ℝ

/-- The nested distribution comparison pairs against the actual double-pullback test map. -/
@[simp]
theorem nestedComparisonCLM_apply {D : Opens M} (h : U ≤ D)
    (T : TauCeti.BundleDistribution I U F
      ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V))
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ)
      (localCoefficients (I := I)
        (V := (⟨Subtype.val, continuous_subtypeVal⟩ : C(D, M)) *ᵖ V)
        (U := Opens.comap (⟨Subtype.val, continuous_subtypeVal⟩ : C(D, M)) U))) :
    nestedComparisonCLM (I := I) (F := F) (V := V) h T s =
      T (nestedTestCLE (I := I) (F := F) (V := V) h s) := by
  exact ContinuousLinearMap.precompCompactConvergenceCLM_apply_apply _ _ _

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
  calc
    _ = restrictCLM (I := I) (F := F) (V := V) (U := U) T
        (nestedTestCLE (I := I) (F := F) (V := V) h s) :=
      nestedComparisonCLM_apply h _ s
    _ = T (testExtensionCLM (I := I) (F := F) (V := V) (U := U)
        (nestedTestCLE (I := I) (F := F) (V := V) h s)) := restrictCLM_apply _ _
    _ = T (testExtensionCLM (I := I) (F := F) (V := V) (U := D)
        (testExtensionCLM (I := I) (F := F) (M := D)
          (V := (⟨Subtype.val, continuous_subtypeVal⟩ : C(D, M)) *ᵖ V) s)) :=
      congrArg T (congrArg (fun L ↦ L s)
        (testExtensionCLM_nested (I := I) (F := F) (V := V) h))
    _ = _ := by erw [restrictCLM_apply, restrictCLM_apply]

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

/-- Universal intrinsic test comparison evaluates by the open density comparison. -/
@[simp]
theorem univTestCLE_apply
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ)
      (localCoefficients (I := I) (V := V) (U := ⊤))) (x : M) :
    univTestCLE (I := I) (F := F) (V := V) s x =
      TauCeti.DensityBundle.openHomEquiv ⟨x, Set.mem_univ x⟩
        (s ⟨x, Set.mem_univ x⟩) := by
  -- Universal intrinsic transport is the composite of density transport and generic tests.
  change TauCeti.BundleTest.univCLE (I := I) (F := F →L[ℝ] ℝ)
    (V := ambientCoefficients (I := I) (V := V)) (openDensityHomCLE s) x = _
  rw [TauCeti.BundleTest.univCLE_apply]
  exact openDensityHomCLE_apply s ⟨x, Set.mem_univ x⟩

/-- The inverse universal intrinsic test comparison evaluates by inverse density transport. -/
@[simp]
theorem univTestCLE_symm_apply
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) (ambientCoefficients (I := I) (V := V)))
    (x : (⊤ : Opens M)) :
    dsimp% only [ContinuousMap.coe_mk] (
    (univTestCLE (I := I) (F := F) (V := V)).symm s x =
      (TauCeti.DensityBundle.openHomEquiv x).symm (s (x : M))) := by
  -- This composition is evaluated before applying the public inverse-density law.
  change (openDensityHomCLE (I := I) (F := F) (V := V) (U := ⊤)).symm
    ((TauCeti.BundleTest.univCLE (I := I) (F := F →L[ℝ] ℝ)
      (V := ambientCoefficients (I := I) (V := V))).symm s) x = _
  erw [openDensityHomCLE_symm_apply]
  exact congrArg (TauCeti.DensityBundle.openHomEquiv (I := I) (V := V) x).symm
    (TauCeti.BundleTest.univCLE_symm_apply (I := I) (F := F →L[ℝ] ℝ)
      (V := ambientCoefficients (I := I) (V := V)) s x)

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
    -- Evaluate the transpose pair before the public inverse law for the test equivalence.
    change T (e.symm (e s)) = T s
    exact congrArg T (e.symm_apply_apply s)
  · apply ContinuousLinearMap.ext
    intro T
    apply ContinuousLinearMap.ext
    intro s
    -- Evaluate the transpose pair before the public inverse law for the test equivalence.
    change T (e (e.symm s)) = T s
    exact congrArg T (e.apply_symm_apply s)

/-- Universal-open distribution restriction pairs against the intrinsic test comparison. -/
@[simp]
theorem univCLE_apply (T : TauCeti.BundleDistribution I M F V)
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ)
      (localCoefficients (I := I) (V := V) (U := ⊤))) :
    univCLE (I := I) (F := F) (V := V) T s =
      T (univTestCLE (I := I) (F := F) (V := V) s) := by
  exact ContinuousLinearMap.precompCompactConvergenceCLM_apply_apply _ _ _

/-- The inverse universal-open comparison pairs against the inverse test comparison. -/
@[simp]
theorem univCLE_symm_apply
    (T : TauCeti.BundleDistribution I (⊤ : Opens M) F
      ((⟨Subtype.val, continuous_subtypeVal⟩ : C((⊤ : Opens M), M)) *ᵖ V))
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) (ambientCoefficients (I := I) (V := V))) :
    (univCLE (I := I) (F := F) (V := V)).symm T s =
      T ((univTestCLE (I := I) (F := F) (V := V)).symm s) := by
  exact ContinuousLinearMap.precompCompactConvergenceCLM_apply_apply _ _ _

/-- The universal-open equivalence has the actual intrinsic restriction as its forward map. -/
theorem univCLE_toContinuousLinearMap :
    (univCLE (I := I) (F := F) (V := V)).toContinuousLinearMap =
      restrictCLM (I := I) (F := F) (V := V) (U := ⊤) := by
  apply ContinuousLinearMap.ext
  intro T
  apply ContinuousLinearMap.ext
  intro s
  erw [restrictCLM_apply]
  -- Both sides pair with native extension after the same density comparison; the forward map
  -- of the universal intrinsic equivalence is defined as that composite.
  change T ((TauCeti.BundleTest.univCLE (I := I) (F := F →L[ℝ] ℝ)
    (V := ambientCoefficients (I := I) (V := V)))
      (openDensityHomCLE (I := I) (F := F) (V := V) s)) =
    T (testExtensionCLM (I := I) (F := F) (V := V) s)
  have h := congrArg (fun L ↦ L (openDensityHomCLE (I := I) (F := F) (V := V) s))
    (TauCeti.BundleTest.univCLE_toContinuousLinearMap (I := I) (F := F →L[ℝ] ℝ)
      (V := ambientCoefficients (I := I) (V := V)))
  exact congrArg T h

end TauCeti.BundleDistribution
