/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.ExtendByZero.Topology
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Map.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Map.CompactSupport
public import TauCeti.Geometry.Manifold.VectorBundle.Density.OpenSubset
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset

/-!
# Restriction of native bundle distributions

Intrinsic dual-density tests on an open subset `U` are identified with tests valued in the
pullback of the ambient dual densities (`TauCeti.BundleTest.openDensityHomCLE`, the native
transport `TauCeti.BundleTest.mapCLE` of `TauCeti.DensityBundle.openHomEquiv`). Followed by native
extension by zero this gives `TauCeti.BundleDistribution.testExtensionCLM`, and its
compact-convergence transpose is restriction of native bundle distributions,
`TauCeti.BundleDistribution.restrictCLM`.

Restriction is compatible with point masses, smooth multipliers, nested opens
(`TauCeti.BundleDistribution.restrictCLM_nested`, through the comparison
`TauCeti.BundleDistribution.nestedTestCLE` of intrinsic tests on the double pullback) and the
universal open (`TauCeti.BundleDistribution.univCLE`).
-/

public noncomputable section

open Bundle FiberBundle Filter Set Topology TopologicalSpace ContMDiffSection
open scoped Manifold ContDiff TauCeti.ManifoldWeakWhitney CompactConvergenceCLM
open TauCeti.DensityBundle (openHomBundle ambientHomBundle pullbackAmbientHomBundle)

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

/-- The preferred trivializations of the intrinsic dual densities. -/
private abbrev intrinsicFrame (x : U) :=
  trivializationAt (F →L[ℝ] ℝ) (openHomBundle (I := I) (V := V) (U := U)) x

/-- The preferred trivializations of the pulled-back ambient dual densities. -/
private abbrev pulledFrame (x : U) :=
  trivializationAt (F →L[ℝ] ℝ) (pullbackAmbientHomBundle (I := I) (V := V) (U := U)) x

/-- A neighbourhood of `x` on which the open dual-density comparison has the identity as
coordinate expression in the two preferred frames at `x`. -/
private def coefficientFrameDomain (x : U) : Opens U :=
  ⟨(intrinsicFrame (I := I) (F := F) (V := V) x).baseSet ∩
    (pulledFrame (I := I) (F := F) (V := V) x).baseSet ∩
    interior {y | ∀ ℓ : openHomBundle (I := I) (V := V) (U := U) y,
      (trivializationAt (F →L[ℝ] ℝ) (ambientHomBundle (I := I) (V := V)) (x : M)
        ⟨(y : M), TauCeti.DensityBundle.openHomEquiv y ℓ⟩).2 =
      (intrinsicFrame (I := I) (F := F) (V := V) x ⟨y, ℓ⟩).2},
    ((intrinsicFrame (I := I) (F := F) (V := V) x).open_baseSet.inter
      (pulledFrame (I := I) (F := F) (V := V) x).open_baseSet).inter isOpen_interior⟩

omit [ContMDiffVectorBundle ∞ F V I] in
private theorem mem_coefficientFrameDomain (x : U) :
    x ∈ coefficientFrameDomain (I := I) (F := F) (V := V) x :=
  ⟨⟨mem_baseSet_trivializationAt _ _ _, mem_baseSet_trivializationAt (F →L[ℝ] ℝ)
      (ambientHomBundle (I := I) (V := V)) (x : M)⟩,
    mem_interior_iff_mem_nhds.mpr
      (TauCeti.DensityBundle.eventually_openHomEquiv_trivializationAt_eq (I := I) (F := F) x)⟩

/-- The open dual-density comparison as a fibrewise linear equivalence onto the pullback. -/
private abbrev openHomLinearEquiv (x : U) :
    openHomBundle (I := I) (V := V) (U := U) x ≃ₗ[ℝ]
      pullbackAmbientHomBundle (I := I) (V := V) (U := U) x :=
  (TauCeti.DensityBundle.openHomEquiv x).toLinearEquiv

omit [ContMDiffVectorBundle ∞ F V I] in
private theorem contMDiff_openHomEquiv :
    ContMDiff (I.prod 𝓘(ℝ, F →L[ℝ] ℝ)) (I.prod 𝓘(ℝ, F →L[ℝ] ℝ)) ∞
      (fun p : TotalSpace (F →L[ℝ] ℝ) (openHomBundle (I := I) (V := V) (U := U)) ↦
        (⟨p.proj, TauCeti.DensityBundle.openHomEquiv p.proj p.snd⟩ :
          TotalSpace (F →L[ℝ] ℝ) (pullbackAmbientHomBundle (I := I) (V := V) (U := U)))) :=
  (TauCeti.DensityBundle.openHomDiffeomorph (I := I) (F := F) (V := V)).contMDiff.congr
    fun p ↦ (TauCeti.DensityBundle.openHomDiffeomorph_apply p).symm

omit [ContMDiffVectorBundle ∞ F V I] in
private theorem contMDiff_openHomEquiv_symm :
    ContMDiff (I.prod 𝓘(ℝ, F →L[ℝ] ℝ)) (I.prod 𝓘(ℝ, F →L[ℝ] ℝ)) ∞
      (fun p : TotalSpace (F →L[ℝ] ℝ) (pullbackAmbientHomBundle (I := I) (V := V) (U := U)) ↦
        (⟨p.proj, (TauCeti.DensityBundle.openHomEquiv p.proj).symm p.snd⟩ :
          TotalSpace (F →L[ℝ] ℝ) (openHomBundle (I := I) (V := V) (U := U)))) :=
  (TauCeti.DensityBundle.openHomDiffeomorph (I := I) (F := F) (V := V)).symm.contMDiff.congr
    fun p ↦ (TauCeti.DensityBundle.openHomDiffeomorph_symm_apply p).symm

omit [ContMDiffVectorBundle ∞ F V I] in
private theorem coefficientFrameDomain_subset_intrinsic (i : U) :
    (coefficientFrameDomain (I := I) (F := F) (V := V) i : Set U) ⊆
      (intrinsicFrame (I := I) (F := F) (V := V) i).baseSet :=
  fun _ h ↦ h.1.1

omit [ContMDiffVectorBundle ∞ F V I] in
private theorem coefficientFrameDomain_subset_pulled (i : U) :
    (coefficientFrameDomain (I := I) (F := F) (V := V) i : Set U) ⊆
      (pulledFrame (I := I) (F := F) (V := V) i).baseSet :=
  fun _ h ↦ h.1.2

/-- On the comparison domain, the open dual-density comparison has the identity as frame
expression. -/
private theorem frameCoordinates_mapEquiv_openHomEquiv (i : U)
    (s : Cₛ^∞⟮I; F →L[ℝ] ℝ, openHomBundle (I := I) (V := V) (U := U)⟯)
    (y : coefficientFrameDomain (I := I) (F := F) (V := V) i) :
    (pulledFrame (I := I) (F := F) (V := V) i).frameCoordinates
      (coefficientFrameDomain_subset_pulled i)
      (mapEquiv (openHomLinearEquiv (I := I) (V := V) (U := U))
        contMDiff_openHomEquiv contMDiff_openHomEquiv_symm s) y =
    (intrinsicFrame (I := I) (F := F) (V := V) i).frameCoordinates
      (coefficientFrameDomain_subset_intrinsic i) s y := by
  rw [Trivialization.frameCoordinates_apply, Trivialization.frameCoordinates_apply]
  -- After `frameCoordinates_apply` the goal is not type-correct at `rw`'s transparency (the
  -- section is read in the unfolded pullback fibre), so `rw` cannot abstract `mapEquiv_apply`.
  erw [mapEquiv_apply]
  -- The preferred pulled-back frame at `i` is the pullback of the ambient frame at `i`.
  exact (interior_subset y.property.2) (s y)

/-- On the comparison domain, the inverse comparison has the identity as frame expression. -/
private theorem frameCoordinates_mapEquiv_openHomEquiv_symm (i : U)
    (s : Cₛ^∞⟮I; F →L[ℝ] ℝ, pullbackAmbientHomBundle (I := I) (V := V) (U := U)⟯)
    (y : coefficientFrameDomain (I := I) (F := F) (V := V) i) :
    (intrinsicFrame (I := I) (F := F) (V := V) i).frameCoordinates
      (coefficientFrameDomain_subset_intrinsic i)
      ((mapEquiv (openHomLinearEquiv (I := I) (V := V) (U := U))
        contMDiff_openHomEquiv contMDiff_openHomEquiv_symm).symm s) y =
    (pulledFrame (I := I) (F := F) (V := V) i).frameCoordinates
      (coefficientFrameDomain_subset_pulled i) s y := by
  rw [Trivialization.frameCoordinates_apply, Trivialization.frameCoordinates_apply]
  -- After `frameCoordinates_apply` the goal is not type-correct at `rw`'s transparency (the
  -- section is read in the unfolded pullback fibre), so `rw` cannot abstract `mapEquiv_symm`.
  erw [mapEquiv_symm, mapEquiv_apply]
  have h := (interior_subset y.property.2) ((TauCeti.DensityBundle.openHomEquiv (y : U)).symm (s y))
  -- The fibre is displayed as `ambientHomBundle (y : M)` rather than the codomain of
  -- `openHomEquiv y`, which `rw` does not identify.
  erw [ContinuousLinearEquiv.apply_symm_apply] at h
  -- The preferred pulled-back frame at `i` is the pullback of the ambient frame at `i`.
  exact h.symm

/-- Intrinsic dual-density tests identify continuously with tests valued in the pullback
of the ambient dual-density bundle. This is the native transport `TauCeti.BundleTest.mapCLE`
of `TauCeti.DensityBundle.openHomEquiv`, whose frame expression is the identity near each
point. -/
def openDensityHomCLE :
    TauCeti.BundleTest I (F →L[ℝ] ℝ) (openHomBundle (I := I) (V := V) (U := U)) ≃L[ℝ]
      TauCeti.BundleTest I (F →L[ℝ] ℝ) (pullbackAmbientHomBundle (I := I) (V := V) (U := U)) :=
  TauCeti.BundleTest.mapCLE (I := I)
    (intrinsicFrame (I := I) (F := F) (V := V)) (pulledFrame (I := I) (F := F) (V := V))
    (coefficientFrameDomain (I := I) (F := F) (V := V)) coefficientFrameDomain_subset_intrinsic
    coefficientFrameDomain_subset_pulled
    (fun x ↦ ⟨x, mem_coefficientFrameDomain x⟩)
    (openHomLinearEquiv (I := I) (V := V) (U := U))
    contMDiff_openHomEquiv contMDiff_openHomEquiv_symm
    (fun _ ↦ ContMDiffMap.const (ContinuousLinearMap.id ℝ (F →L[ℝ] ℝ)))
    (fun _ ↦ ContMDiffMap.const (ContinuousLinearMap.id ℝ (F →L[ℝ] ℝ)))
    frameCoordinates_mapEquiv_openHomEquiv frameCoordinates_mapEquiv_openHomEquiv_symm

/-- The intrinsic test comparison evaluates by the native pointwise open-density map. -/
@[simp]
theorem openDensityHomCLE_apply
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) (openHomBundle (I := I) (V := V) (U := U))) (x : U) :
    openDensityHomCLE (I := I) (F := F) (V := V) s x =
      TauCeti.DensityBundle.openHomEquiv x (s x) := by
  -- `mapCLE` takes the fibre instances of a generic bundle; on the density Hom abbreviations they
  -- agree with the displayed ones only after unfolding, which `rw` does not do.
  erw [openDensityHomCLE, mapCLE_apply]
  -- `openHomLinearEquiv x` is the underlying linear equivalence of `openHomEquiv x`.
  rfl

/-- The inverse intrinsic test comparison evaluates by the inverse native density map. -/
@[simp]
theorem openDensityHomCLE_symm_apply
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) (pullbackAmbientHomBundle (I := I) (V := V) (U := U)))
    (x : U) :
    (openDensityHomCLE (I := I) (F := F) (V := V)).symm s x =
      (TauCeti.DensityBundle.openHomEquiv x).symm (s x) := by
  -- `mapCLE` takes the fibre instances of a generic bundle; on the density Hom abbreviations they
  -- agree with the displayed ones only after unfolding, which `rw` does not do.
  erw [openDensityHomCLE, mapCLE_symm_apply]
  -- `(openHomLinearEquiv x).symm` is the underlying linear equivalence of `(openHomEquiv x).symm`.
  rfl

/-- The intrinsic test comparison vanishes exactly where the test vanishes. -/
theorem openDensityHomCLE_apply_ne_zero_iff
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) (openHomBundle (I := I) (V := V) (U := U))) (x : U) :
    openDensityHomCLE (I := I) (F := F) (V := V) s x ≠ 0 ↔ s x ≠ 0 := by
  rw [openDensityHomCLE_apply]
  exact (TauCeti.DensityBundle.openHomEquiv (I := I) (V := V) x).toLinearEquiv.map_ne_zero_iff

/-- The inverse intrinsic test comparison vanishes exactly where the test vanishes. -/
theorem openDensityHomCLE_symm_apply_ne_zero_iff
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) (pullbackAmbientHomBundle (I := I) (V := V) (U := U)))
    (x : U) :
    (openDensityHomCLE (I := I) (F := F) (V := V)).symm s x ≠ 0 ↔ s x ≠ 0 := by
  rw [openDensityHomCLE_symm_apply]
  exact (TauCeti.DensityBundle.openHomEquiv (I := I) (V := V) x).symm.toLinearEquiv.map_ne_zero_iff

/-- The intrinsic density comparison commutes with multiplication by smooth real functions. -/
theorem openDensityHomCLE_smulLeftCLM (f : C^∞⟮I, U; ℝ⟯)
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) (openHomBundle (I := I) (V := V) (U := U))) :
    openDensityHomCLE (I := I) (F := F) (V := V) (TauCeti.BundleTest.smulLeftCLM f s) =
      TauCeti.BundleTest.smulLeftCLM f (openDensityHomCLE (I := I) (F := F) (V := V) s) := by
  apply TauCeti.BundleTest.ext
  intro x
  rw [openDensityHomCLE_apply, smulLeftCLM_apply, smulLeftCLM_apply, openDensityHomCLE_apply,
    map_smul]
  -- Both sides now display the same fibre value through different carrier abbreviations.
  rfl

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
    TauCeti.BundleTest I (F →L[ℝ] ℝ) ((openHomBundle (I := I) (V := V) (U := U))) →L[ℝ]
      TauCeti.BundleTest I (F →L[ℝ] ℝ) ((ambientHomBundle (I := I) (V := V))) := by
  exact (TauCeti.BundleTest.extendByZeroCLM (I := I) (F := F →L[ℝ] ℝ)
    (V := ambientHomBundle (I := I) (V := V)) (U := U)).comp
    (openDensityHomCLE (I := I) (F := F) (V := V) (U := U)).toContinuousLinearMap

/-- Intrinsic test extension is native extension after the open density comparison. -/
theorem testExtensionCLM_apply
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) ((openHomBundle (I := I) (V := V) (U := U)))) :
    testExtensionCLM (I := I) (F := F) (V := V) s =
      TauCeti.BundleTest.extendByZeroCLM (I := I) (F := F →L[ℝ] ℝ)
        (V := ambientHomBundle (I := I) (V := V)) (U := U)
        (openDensityHomCLE (I := I) (F := F) (V := V) s) :=
  (rfl)

/-- On the open subset, intrinsic extension evaluates by the native density comparison. -/
@[simp]
theorem testExtensionCLM_apply_of_mem
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) ((openHomBundle (I := I) (V := V) (U := U))))
    (x : U) :
    testExtensionCLM (I := I) (F := F) (V := V) s (x : M) =
      TauCeti.DensityBundle.openHomEquiv x (s x) := by
  rw [testExtensionCLM_apply, TauCeti.BundleTest.extendByZeroCLM_apply_of_mem]
  exact openDensityHomCLE_apply s x

/-- Intrinsic test extension vanishes outside the open subset. -/
@[simp]
theorem testExtensionCLM_apply_of_notMem
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) ((openHomBundle (I := I) (V := V) (U := U))))
    {x : M} (hx : x ∉ U) :
    testExtensionCLM (I := I) (F := F) (V := V) s x = 0 := by
  rw [testExtensionCLM_apply]
  exact TauCeti.BundleTest.extendByZeroCLM_apply_of_notMem (I := I) (F := F →L[ℝ] ℝ)
    (V := ambientHomBundle (I := I) (V := V))
    (openDensityHomCLE (I := I) (F := F) (V := V) s) hx

/-- Restriction of native bundle distributions, obtained by compact-convergence transpose
of intrinsic dual-density test extension. -/
def restrictCLM :
    TauCeti.BundleDistribution I M F V →L[ℝ]
      TauCeti.BundleDistribution I U F ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V) :=
  ((openDensityHomCLE (I := I) (F := F) (V := V)
    (U := U)).toContinuousLinearMap.precompCompactConvergenceCLM ℝ).comp
      (restrictDualCLM (I := I) (F := F →L[ℝ] ℝ)
        (V := ambientHomBundle (I := I) (V := V)) (W := ℝ) (U := U))

/-- Restriction is dual restriction precomposed with the intrinsic density comparison. -/
theorem restrictCLM_apply_eq_restrictDualCLM (T : TauCeti.BundleDistribution I M F V)
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) (openHomBundle (I := I) (V := V) (U := U))) :
    restrictCLM (I := I) (F := F) (V := V) T s =
      restrictDualCLM (I := I) (F := F →L[ℝ] ℝ) (V := ambientHomBundle (I := I) (V := V))
        (W := ℝ) (U := U) T (openDensityHomCLE (I := I) (F := F) (V := V) s) :=
  ContinuousLinearMap.precompCompactConvergenceCLM_apply_apply _ _ _

/-- Restriction pairs with an intrinsic test by pairing with its ambient extension. -/
@[simp]
theorem restrictCLM_apply (T : TauCeti.BundleDistribution I M F V)
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) (openHomBundle (I := I) (V := V) (U := U))) :
    restrictCLM (I := I) (F := F) (V := V) T s =
      T (testExtensionCLM (I := I) (F := F) (V := V) s) :=
  (restrictCLM_apply_eq_restrictDualCLM T s).trans
    ((restrictDualCLM_apply T _).trans (congrArg T (testExtensionCLM_apply s).symm))

/-- A point mass inside the open subset restricts by transposing the native density map. -/
@[simp]
theorem restrictCLM_delta_of_mem (x : U)
    (ℓ : ambientHomBundle (I := I) (V := V) (x : M) →L[ℝ] ℝ) :
    restrictCLM (I := I) (F := F) (V := V) (U := U)
        (TauCeti.BundleTest.delta (I := I) (F := F →L[ℝ] ℝ) (x : M) ℓ) =
      TauCeti.BundleTest.delta (I := I) (F := F →L[ℝ] ℝ)
        (V := openHomBundle (I := I) (V := V) (U := U)) x
        (ℓ.comp
          (TauCeti.DensityBundle.openHomEquiv (I := I) (V := V) x).toContinuousLinearMap) := by
  refine DFunLike.ext _ _ fun s ↦ ?_
  rw [restrictCLM_apply_eq_restrictDualCLM, restrictDualCLM_delta_of_mem, delta_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  -- `restrictDualCLM_delta_of_mem` states its point mass on the unbundled pullback
  -- `Subtype.val *ᵖ ambientHomBundle`, which carries no bundle instances for `rw`, so
  -- `delta_apply` is instantiated on `pullbackAmbientHomBundle` explicitly.
  refine (delta_apply (I := I) (F := F →L[ℝ] ℝ)
    (V := pullbackAmbientHomBundle (I := I) (V := V) (U := U)) (W := ℝ) x ℓ _).trans ?_
  exact congrArg ℓ (openDensityHomCLE_apply s x)

/-- A point mass outside the open subset restricts to zero. -/
@[simp]
theorem restrictCLM_delta_of_notMem {x : M} (hx : x ∉ U)
    (ℓ : ambientHomBundle (I := I) (V := V) x →L[ℝ] ℝ) :
    restrictCLM (I := I) (F := F) (V := V) (U := U)
      (TauCeti.BundleTest.delta (I := I) (F := F →L[ℝ] ℝ) x ℓ) = 0 := by
  refine DFunLike.ext _ _ fun s ↦ ?_
  rw [restrictCLM_apply_eq_restrictDualCLM, restrictDualCLM_delta_of_notMem _ _ hx,
    _root_.zero_apply, _root_.zero_apply]

/-- The topological support of intrinsic test extension is exactly the included support. -/
@[simp]
theorem tsupport_testExtensionCLM
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) (openHomBundle (I := I) (V := V) (U := U))) :
    closure {x : M | testExtensionCLM (I := I) (F := F) (V := V) s x ≠ 0} =
      Subtype.val '' closure {x : U | s x ≠ 0} := by
  simp only [testExtensionCLM_apply]
  refine (TauCeti.BundleTest.tsupport_extendByZeroCLM (I := I) (F := F →L[ℝ] ℝ)
    (V := ambientHomBundle (I := I) (V := V)) (U := U)
    (openDensityHomCLE (I := I) (F := F) (V := V) s)).trans ?_
  congr 2
  ext x
  exact openDensityHomCLE_apply_ne_zero_iff s x

/-- Native distribution restriction commutes with smooth real multiplication. -/
theorem restrictCLM_smulLeftDualCLM (f : C^∞⟮I, M; ℝ⟯) (T : TauCeti.BundleDistribution I M F V) :
    restrictCLM (I := I) (F := F) (V := V) (U := U)
        (TauCeti.BundleTest.smulLeftDualCLM (I := I) (F := F →L[ℝ] ℝ)
          (V := ambientHomBundle (I := I) (V := V)) f T) =
      TauCeti.BundleTest.smulLeftDualCLM (I := I) (F := F →L[ℝ] ℝ)
        (V := openHomBundle (I := I) (V := V) (U := U)) (f.restrict U)
        (restrictCLM (I := I) (F := F) (V := V) (U := U) T) := by
  refine DFunLike.ext _ _ fun s ↦ ?_
  rw [restrictCLM_apply_eq_restrictDualCLM, restrictDualCLM_smulLeftDualCLM, smulLeftDualCLM_apply,
    smulLeftDualCLM_apply, restrictCLM_apply_eq_restrictDualCLM, openDensityHomCLE_smulLeftCLM]

omit [T2Space M] in
/-- `localizeCLM_apply` for tests valued in the ambient dual densities, read on
`pullbackAmbientHomBundle`. -/
private theorem localizeCLM_ambientHomBundle_apply {N : Type*} [TopologicalSpace N]
    [ChartedSpace H N] [IsManifold I ∞ N] {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {Z : N → Type*} [∀ x, AddCommGroup (Z x)] [∀ x, Module ℝ (Z x)]
    [∀ x, TopologicalSpace (Z x)] [TopologicalSpace (TotalSpace G Z)] [FiberBundle G Z]
    [VectorBundle ℝ G Z] [ContMDiffVectorBundle ∞ G Z I]
    (T : TauCeti.BundleTest I G Z →L[ℝ]
      TauCeti.BundleTest I (F →L[ℝ] ℝ) (ambientHomBundle (I := I) (V := V)))
    (q : C(N, U)) (hT : ∀ s, closure {x : M | T s x ≠ 0} ⊆
      Subtype.val '' q '' closure {x : N | s x ≠ 0})
    (s : TauCeti.BundleTest I G Z) (u : U) :
    TauCeti.BundleTest.localizeCLM (I := I) (F := F →L[ℝ] ℝ)
      (V := ambientHomBundle (I := I) (V := V)) T q hT s u = T s (u : M) := by
  -- `localizeCLM_apply` is stated (in `dsimp%` form) on the unbundled pullback `Subtype.val *ᵖ V`,
  -- which `rw` does not match against `pullbackAmbientHomBundle`.
  erw [TauCeti.BundleTest.localizeCLM_apply]

private def intrinsicInclusionCLM {D : Opens M} (h : U ≤ D) :
    TauCeti.BundleTest I (F →L[ℝ] ℝ) (openHomBundle (I := I) (V := V) (U := U)) →L[ℝ]
      TauCeti.BundleTest I (F →L[ℝ] ℝ) (openHomBundle (I := I) (V := V) (U := D)) := by
  exact (openDensityHomCLE (I := I) (F := F) (V := V) (U := D)).symm.toContinuousLinearMap.comp
    ((TauCeti.BundleTest.extendByZeroToOpenCLM (I := I) (F := F →L[ℝ] ℝ)
      (V := ambientHomBundle (I := I) (V := V)) h).comp
      (openDensityHomCLE (I := I) (F := F) (V := V) (U := U)).toContinuousLinearMap)

private theorem intrinsicInclusionCLM_eq {D : Opens M} (h : U ≤ D)
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) (openHomBundle (I := I) (V := V) (U := U))) :
    intrinsicInclusionCLM (I := I) (F := F) (V := V) h s =
      (openDensityHomCLE (I := I) (F := F) (V := V) (U := D)).symm
        (extendByZeroToOpenCLM (I := I) (F := F →L[ℝ] ℝ)
          (V := ambientHomBundle (I := I) (V := V)) h
          (openDensityHomCLE (I := I) (F := F) (V := V) s)) :=
  rfl

private abbrev nestedOpen (U D : Opens M) : Opens D :=
  Opens.comap (⟨Subtype.val, continuous_subtypeVal⟩ : C(D, M)) U

private abbrev doubleHomBundle (D : Opens M) :=
  openHomBundle (I := I) (V := (⟨Subtype.val, continuous_subtypeVal⟩ : C(D, M)) *ᵖ V)
    (U := nestedOpen U D)

private def iteratedIntrinsicTestExtensionCLM (D : Opens M) :
    TauCeti.BundleTest I (F →L[ℝ] ℝ) (doubleHomBundle (I := I) (V := V) (U := U) D) →L[ℝ]
      TauCeti.BundleTest I (F →L[ℝ] ℝ) (ambientHomBundle (I := I) (V := V)) :=
  (testExtensionCLM (I := I) (F := F) (V := V) (U := D)).comp
    (testExtensionCLM (I := I) (F := F) (M := D)
      (V := (⟨Subtype.val, continuous_subtypeVal⟩ : C(D, M)) *ᵖ V) (U := nestedOpen U D))

private theorem iteratedIntrinsicTestExtensionCLM_apply (D : Opens M)
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) (doubleHomBundle (I := I) (V := V) (U := U) D)) :
    iteratedIntrinsicTestExtensionCLM (I := I) (F := F) (V := V) D s =
      testExtensionCLM (I := I) (F := F) (V := V) (U := D)
        (testExtensionCLM (I := I) (F := F) (M := D)
          (V := (⟨Subtype.val, continuous_subtypeVal⟩ : C(D, M)) *ᵖ V) (U := nestedOpen U D) s) :=
  rfl

private theorem tsupport_iteratedIntrinsicTestExtensionCLM {D : Opens M} (h : U ≤ D)
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) (doubleHomBundle (I := I) (V := V) (U := U) D)) :
    closure {x : M | iteratedIntrinsicTestExtensionCLM (I := I) (F := F) (V := V) D s x ≠ 0} =
      Subtype.val '' (Diffeomorph.nestedOpen (I := I) (n := ∞) h) ''
        closure {x : nestedOpen U D | s x ≠ 0}
        := by
  simp only [iteratedIntrinsicTestExtensionCLM_apply]
  rw [tsupport_testExtensionCLM (I := I) (F := F) (V := V) (U := D)]
  rw [tsupport_testExtensionCLM (I := I) (F := F) (M := D)
    (V := (⟨Subtype.val, continuous_subtypeVal⟩ : C(D, M)) *ᵖ V) (U := nestedOpen U D)]
  rw [Set.image_image, Set.image_image]
  simp only [Diffeomorph.nestedOpen_apply]

private def intrinsicNestedTestComparisonCLM {D : Opens M} (h : U ≤ D) :
    TauCeti.BundleTest I (F →L[ℝ] ℝ) (doubleHomBundle (I := I) (V := V) (U := U) D) →L[ℝ]
      TauCeti.BundleTest I (F →L[ℝ] ℝ) (openHomBundle (I := I) (V := V) (U := U)) := by
  let q : C(nestedOpen U D, U) := ⟨Diffeomorph.nestedOpen (I := I) (n := ∞) h,
    (Diffeomorph.nestedOpen (I := I) (n := ∞) h).continuous⟩
  exact (openDensityHomCLE (I := I) (F := F) (V := V) (U := U)).symm.toContinuousLinearMap.comp
    (TauCeti.BundleTest.localizeCLM (I := I) (F := F →L[ℝ] ℝ)
      (V := ambientHomBundle (I := I) (V := V))
      (iteratedIntrinsicTestExtensionCLM (I := I) (F := F) (V := V) D) q
      (fun s ↦ (tsupport_iteratedIntrinsicTestExtensionCLM h s).le))

private theorem intrinsicNestedTestComparisonCLM_apply {D : Opens M} (h : U ≤ D)
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) (doubleHomBundle (I := I) (V := V) (U := U) D))
    (x : nestedOpen U D) :
    intrinsicNestedTestComparisonCLM (I := I) (F := F) (V := V) h s
      (⟨x.val.val, x.property⟩ : U) =
    (TauCeti.DensityBundle.openHomEquiv (I := I) (V := V) (⟨x.val.val, x.property⟩ : U)).symm
      (TauCeti.DensityBundle.openHomEquiv (I := I) (V := V) x.val
        (TauCeti.DensityBundle.openHomEquiv (I := I) (M := D)
          (V := (⟨Subtype.val, continuous_subtypeVal⟩ : C(D, M)) *ᵖ V) x (s x))) := by
  unfold intrinsicNestedTestComparisonCLM
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, openDensityHomCLE_symm_apply]
  rw [localizeCLM_ambientHomBundle_apply]
  congr 1
  rw [iteratedIntrinsicTestExtensionCLM_apply]
  rw [testExtensionCLM_apply_of_mem _ x.val,
    testExtensionCLM_apply_of_mem s x]

private theorem tsupport_intrinsicInclusionCLM {D : Opens M} (h : U ≤ D)
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) (openHomBundle (I := I) (V := V) (U := U))) :
    closure {x : D | intrinsicInclusionCLM (I := I) (F := F) (V := V) h s x ≠ 0} =
      (Opens.inclusion h) '' closure {x : U | s x ≠ 0} := by
  let t := extendByZeroToOpenCLM (I := I) (F := F →L[ℝ] ℝ)
    (V := ambientHomBundle (I := I) (V := V)) h
    (openDensityHomCLE (I := I) (F := F) (V := V) s)
  have hset : {x : D | intrinsicInclusionCLM (I := I) (F := F) (V := V) h s x ≠ 0} =
      {x : D | t x ≠ 0} := by
    ext x
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, intrinsicInclusionCLM_eq]
    exact openDensityHomCLE_symm_apply_ne_zero_iff t x
  rw [hset, tsupport_extendByZeroToOpenCLM]
  apply congrArg (fun K : Set U ↦ (Opens.inclusion h) '' closure K)
  ext x
  exact openDensityHomCLE_apply_ne_zero_iff s x

private def intrinsicNestedTestInverseCLM {D : Opens M} (h : U ≤ D) :
    TauCeti.BundleTest I (F →L[ℝ] ℝ) (openHomBundle (I := I) (V := V) (U := U)) →L[ℝ]
      TauCeti.BundleTest I (F →L[ℝ] ℝ) (doubleHomBundle (I := I) (V := V) (U := U) D) := by
  let VD := (⟨Subtype.val, continuous_subtypeVal⟩ : C(D, M)) *ᵖ V
  let ND := nestedOpen U D
  let q : C(U, ND) := ⟨(Diffeomorph.nestedOpen (I := I) (n := ∞) h).symm,
    (Diffeomorph.nestedOpen (I := I) (n := ∞) h).symm.continuous⟩
  have hs : ∀ s : TauCeti.BundleTest I (F →L[ℝ] ℝ)
      (openHomBundle (I := I) (V := V) (U := U)),
      closure {x : D | intrinsicInclusionCLM (I := I) (F := F) (V := V) h s x ≠ 0} ⊆
        Subtype.val '' q '' closure {x : U | s x ≠ 0} := by
    intro s
    rw [tsupport_intrinsicInclusionCLM]
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨q u, ⟨u, hu, rfl⟩, ?_⟩
    simp only [q, ContinuousMap.coe_mk, Diffeomorph.nestedOpen_symm_apply, Opens.inclusion]
  exact (openDensityHomCLE (I := I) (F := F) (M := D) (V := VD) (U :=
    ND)).symm.toContinuousLinearMap.comp
    (TauCeti.BundleTest.localizeCLM (I := I) (F := F →L[ℝ] ℝ) (M := D)
      (V := ambientHomBundle (I := I) (M := D) (V := VD))
      (intrinsicInclusionCLM (I := I) (F := F) (V := V) h) q hs)

private theorem intrinsicInclusionCLM_apply {D : Opens M} (h : U ≤ D)
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) (openHomBundle (I := I) (V := V) (U := U)))
    (u : U) : intrinsicInclusionCLM (I := I) (F := F) (V := V) h s (Opens.inclusion h u) =
      (TauCeti.DensityBundle.openHomEquiv (I := I) (V := V) (Opens.inclusion h u)).symm
        (TauCeti.DensityBundle.openHomEquiv (I := I) (V := V) u (s u)) := by
  rw [intrinsicInclusionCLM_eq]
  rw [openDensityHomCLE_symm_apply (I := I) (F := F) (V := V) (U := D)]
  congr 1
  -- `extendByZeroToOpenCLM_apply_of_mem` is stated (in `dsimp%` form) on the unbundled pullback
  -- `Subtype.val *ᵖ V`, which `rw` does not match against `pullbackAmbientHomBundle`.
  erw [extendByZeroToOpenCLM_apply_of_mem, openDensityHomCLE_apply]
  exact Pullback.lift_snd _ _

private theorem intrinsicNestedTestInverseCLM_apply {D : Opens M} (h : U ≤ D)
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) (openHomBundle (I := I) (V := V) (U := U)))
    (x : nestedOpen U D) : intrinsicNestedTestInverseCLM (I := I) (F := F) (V := V) h s x =
      (TauCeti.DensityBundle.openHomEquiv (I := I) (M := D)
        (V := (⟨Subtype.val, continuous_subtypeVal⟩ : C(D, M)) *ᵖ V) x).symm
        ((TauCeti.DensityBundle.openHomEquiv (I := I) (V := V) x.val).symm
          (TauCeti.DensityBundle.openHomEquiv (I := I) (V := V) (⟨x.val.val, x.property⟩ : U)
            (s (⟨x.val.val, x.property⟩ : U)))) := by
  unfold intrinsicNestedTestInverseCLM
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, openDensityHomCLE_symm_apply]
  rw [localizeCLM_ambientHomBundle_apply]
  have hi := intrinsicInclusionCLM_apply (I := I) (F := F) (V := V) h s
    (⟨x.val.val, x.property⟩ : U)
  exact congrArg (TauCeti.DensityBundle.openHomEquiv (I := I) (M := D)
    (V := (⟨Subtype.val, continuous_subtypeVal⟩ : C(D, M)) *ᵖ V) x).symm hi

private theorem intrinsicNestedTestComparison_left_inv {D : Opens M} (h : U ≤ D)
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) (doubleHomBundle (I := I) (V := V) (U := U) D)) :
    intrinsicNestedTestInverseCLM (I := I) (F := F) (V := V) h
      (intrinsicNestedTestComparisonCLM (I := I) (F := F) (V := V) h s) = s := by
  apply TauCeti.BundleTest.ext
  intro x
  rw [intrinsicNestedTestInverseCLM_apply (I := I) (F := F) (V := V) h _ x,
    intrinsicNestedTestComparisonCLM_apply (I := I) (F := F) (V := V) h s x]
  rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply,
    ContinuousLinearEquiv.symm_apply_apply]

private theorem intrinsicNestedTestComparison_right_inv {D : Opens M} (h : U ≤ D)
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) (openHomBundle (I := I) (V := V) (U := U))) :
    intrinsicNestedTestComparisonCLM (I := I) (F := F) (V := V) h
      (intrinsicNestedTestInverseCLM (I := I) (F := F) (V := V) h s) = s := by
  apply TauCeti.BundleTest.ext
  rintro ⟨u, hu⟩
  -- The evaluation lemmas read the point of `U` as the image of this point of `nestedOpen U D`.
  let x : nestedOpen U D := ⟨⟨u, h hu⟩, hu⟩
  rw [intrinsicNestedTestComparisonCLM_apply (I := I) (F := F) (V := V) h _ x,
    intrinsicNestedTestInverseCLM_apply (I := I) (F := F) (V := V) h s x]
  rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.symm_apply_apply]

/-- Identify the intrinsic tests on the actual double pullback with direct intrinsic tests
through native extension, localization, and the tangent-density comparisons. -/
def nestedTestCLE {D : Opens M} (h : U ≤ D) :
    let cD : C(D, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    let N := Opens.comap cD U
    TauCeti.BundleTest I (F →L[ℝ] ℝ)
      (openHomBundle (I := I) (V := cD *ᵖ V) (U := N)) ≃L[ℝ]
      TauCeti.BundleTest I (F →L[ℝ] ℝ)
        (openHomBundle (I := I) (V := V) (U := U)) := by
  intro cD N
  exact ContinuousLinearEquiv.ofContinuousLinearMap
    (intrinsicNestedTestComparisonCLM (I := I) (F := F) (V := V) h)
    (intrinsicNestedTestInverseCLM (I := I) (F := F) (V := V) h)
    (by apply ContinuousLinearMap.ext; intro s; exact intrinsicNestedTestComparison_right_inv h s)
    (by apply ContinuousLinearMap.ext; intro s; exact intrinsicNestedTestComparison_left_inv h s)

/-- The nested comparison is the comparison map it is built from. -/
private theorem nestedTestCLE_apply_eq {D : Opens M} (h : U ≤ D)
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) (doubleHomBundle (I := I) (V := V) (U := U) D)) :
    nestedTestCLE (I := I) (F := F) (V := V) h s =
      intrinsicNestedTestComparisonCLM (I := I) (F := F) (V := V) h s :=
  (rfl)

/-- The inverse nested comparison is the inverse map it is built from. -/
private theorem nestedTestCLE_symm_apply_eq {D : Opens M} (h : U ≤ D)
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) (openHomBundle (I := I) (V := V) (U := U))) :
    (nestedTestCLE (I := I) (F := F) (V := V) h).symm s =
      intrinsicNestedTestInverseCLM (I := I) (F := F) (V := V) h s :=
  (rfl)

omit [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M] in
/-- The three open dual-density comparisons along `nestedOpen U D ⊆ D ⊆ M` and back to `U`
preserve the underlying functional. -/
private theorem openHomEquiv_nested_apply {D : Opens M} (x : nestedOpen U D)
    (ℓ : doubleHomBundle (I := I) (V := V) (U := U) D x) :
    (TauCeti.DensityBundle.openHomEquiv (I := I) (V := V) (⟨x.val.val, x.property⟩ : U)).symm
      (TauCeti.DensityBundle.openHomEquiv (I := I) (V := V) x.val
        (TauCeti.DensityBundle.openHomEquiv (I := I) (M := D)
          (V := (⟨Subtype.val, continuous_subtypeVal⟩ : C(D, M)) *ᵖ V) x ℓ)) = ℓ := by
  -- Over `D` the implicit bundle of `openHomEquiv` is the unfolded pullback
  -- `⇑⟨Subtype.val, _⟩ *ᵖ V`; `rw` and `simp only` do not match the lemma's `cD *ᵖ V` there.
  erw [TauCeti.DensityBundle.openHomEquiv_apply (I := I) (M := D),
    TauCeti.DensityBundle.openHomEquiv_apply (I := I) (V := V),
    TauCeti.DensityBundle.openHomEquiv_symm_apply (I := I) (V := V)]

omit [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M] in
/-- The inverse comparisons from `U` back to `nestedOpen U D` preserve the underlying functional. -/
private theorem openHomEquiv_nested_symm_apply {D : Opens M} (x : nestedOpen U D)
    (ℓ : openHomBundle (I := I) (V := V) (U := U) (⟨x.val.val, x.property⟩ : U)) :
    (TauCeti.DensityBundle.openHomEquiv (I := I) (M := D)
        (V := (⟨Subtype.val, continuous_subtypeVal⟩ : C(D, M)) *ᵖ V) x).symm
      ((TauCeti.DensityBundle.openHomEquiv (I := I) (V := V) x.val).symm
        (TauCeti.DensityBundle.openHomEquiv (I := I) (V := V) (⟨x.val.val, x.property⟩ : U) ℓ)) =
      ℓ := by
  -- Over `D` the implicit bundle of `openHomEquiv` is the unfolded pullback
  -- `⇑⟨Subtype.val, _⟩ *ᵖ V`; `rw` and `simp only` do not match the lemma's `cD *ᵖ V` there.
  erw [TauCeti.DensityBundle.openHomEquiv_apply (I := I) (V := V),
    TauCeti.DensityBundle.openHomEquiv_symm_apply (I := I) (V := V),
    TauCeti.DensityBundle.openHomEquiv_symm_apply (I := I) (M := D)]

/-- The nested comparison preserves each underlying fibrewise functional. -/
@[simp]
theorem nestedTestCLE_apply {D : Opens M} (h : U ≤ D) :
    dsimp% only [ContinuousMap.coe_mk] (
    let cD : C(D, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    let N := Opens.comap cD U
    ∀ (s : TauCeti.BundleTest I (F →L[ℝ] ℝ)
      (openHomBundle (I := I) (V := cD *ᵖ V) (U := N))) (x : N),
      nestedTestCLE (I := I) (F := F) (V := V) h s
        (⟨x.val.val, x.property⟩ : U) = s x) := by
  intro s x
  rw [nestedTestCLE_apply_eq]
  rw [intrinsicNestedTestComparisonCLM_apply (I := I) (F := F) (V := V) h s x]
  exact openHomEquiv_nested_apply x (s x)

/-- The inverse nested comparison evaluates at the canonical nested-base identification. -/
@[simp]
theorem nestedTestCLE_symm_apply {D : Opens M} (h : U ≤ D) :
    dsimp% only [ContinuousMap.coe_mk] (
    let cD : C(D, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    let N := Opens.comap cD U
    ∀ (s : TauCeti.BundleTest I (F →L[ℝ] ℝ)
      (openHomBundle (I := I) (V := V) (U := U))) (x : N),
      (nestedTestCLE (I := I) (F := F) (V := V) h).symm s x =
        s (⟨x.val.val, x.property⟩ : U)) := by
  intro s x
  rw [nestedTestCLE_symm_apply_eq]
  exact (intrinsicNestedTestInverseCLM_apply (I := I) (F := F) (V := V) h s x).trans
    (openHomEquiv_nested_symm_apply x _)

/-- Actual direct and successive intrinsic test extensions agree through the comparison. -/
theorem testExtensionCLM_nested {D : Opens M} (h : U ≤ D) :
    let cD : C(D, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    let N := Opens.comap cD U
    (testExtensionCLM (I := I) (F := F) (V := V) (U := U)).comp
      (nestedTestCLE (I := I) (F := F) (V := V) h).toContinuousLinearMap =
    (testExtensionCLM (I := I) (F := F) (V := V) (U := D)).comp
      (testExtensionCLM (I := I) (F := F) (M := D) (V := cD *ᵖ V) (U := N)) := by
  intro cD _
  let q : C(nestedOpen U D, U) := ⟨Diffeomorph.nestedOpen (I := I) (n := ∞) h,
    (Diffeomorph.nestedOpen (I := I) (n := ∞) h).continuous⟩
  apply ContinuousLinearMap.ext
  intro s
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, testExtensionCLM_apply,
    ContinuousLinearEquiv.coe_coe, nestedTestCLE_apply_eq,
    ← iteratedIntrinsicTestExtensionCLM_apply]
  unfold intrinsicNestedTestComparisonCLM
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply]
  exact TauCeti.BundleTest.extendByZeroCLM_localizeCLM _ q
    (fun t ↦ (tsupport_iteratedIntrinsicTestExtensionCLM h t).le) s

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
      (openHomBundle (I := I)
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
  refine DFunLike.ext _ _ fun s ↦ ?_
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
    _ = _ := by rw [restrictCLM_apply, restrictCLM_apply]

/-- Intrinsic tests on the universal open subset identify with ambient tests. -/
def univTestCLE :
    let c : C((⊤ : Opens M), M) := ⟨Subtype.val, continuous_subtypeVal⟩
    TauCeti.BundleTest I (F →L[ℝ] ℝ)
      (fun x : (⊤ : Opens M) ↦ (c *ᵖ V) x →L[ℝ] TauCeti.DensityBundle I (⊤ : Opens M) x) ≃L[ℝ]
    TauCeti.BundleTest I (F →L[ℝ] ℝ) (fun x ↦ V x →L[ℝ] TauCeti.DensityBundle I M x) := by
  intro _
  exact (openDensityHomCLE (I := I) (F := F) (V := V) (U := ⊤)).trans
    (TauCeti.BundleTest.univCLE (I := I) (F := F →L[ℝ] ℝ)
      (V := ambientHomBundle (I := I) (V := V)))

/-- Universal intrinsic test comparison evaluates by the open density comparison. -/
@[simp]
theorem univTestCLE_apply
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ)
      (openHomBundle (I := I) (V := V) (U := ⊤))) (x : M) :
    univTestCLE (I := I) (F := F) (V := V) s x =
      TauCeti.DensityBundle.openHomEquiv ⟨x, Set.mem_univ x⟩
        (s ⟨x, Set.mem_univ x⟩) := by
  rw [univTestCLE, ContinuousLinearEquiv.trans_apply, TauCeti.BundleTest.univCLE_apply]
  exact openDensityHomCLE_apply s ⟨x, Set.mem_univ x⟩

/-- `univTestCLE_symm_apply` before `ContinuousMap.coe_mk` normalization: the bundled inclusion
keeps the bundle instances the rewrites in its proof need. -/
private theorem univTestCLE_symm_apply_aux
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) (ambientHomBundle (I := I) (V := V)))
    (x : (⊤ : Opens M)) :
    (univTestCLE (I := I) (F := F) (V := V)).symm s x =
      (TauCeti.DensityBundle.openHomEquiv x).symm (s (x : M)) := by
  rw [univTestCLE, ContinuousLinearEquiv.symm_trans_apply, openDensityHomCLE_symm_apply]
  exact congrArg (TauCeti.DensityBundle.openHomEquiv (I := I) (V := V) x).symm
    (TauCeti.BundleTest.univCLE_symm_apply (I := I) (F := F →L[ℝ] ℝ)
      (V := ambientHomBundle (I := I) (V := V)) s x)

/-- The inverse universal intrinsic test comparison evaluates by inverse density transport. -/
@[simp]
theorem univTestCLE_symm_apply
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) (ambientHomBundle (I := I) (V := V)))
    (x : (⊤ : Opens M)) :
    dsimp% only [ContinuousMap.coe_mk] (
    (univTestCLE (I := I) (F := F) (V := V)).symm s x =
      (TauCeti.DensityBundle.openHomEquiv x).symm (s (x : M))) :=
  univTestCLE_symm_apply_aux s x

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
  · refine ContinuousLinearMap.ext fun T ↦ DFunLike.ext _ _ fun s ↦ ?_
    rw [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.precompCompactConvergenceCLM_apply_apply,
      ContinuousLinearMap.precompCompactConvergenceCLM_apply_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.coe_coe, e.symm_apply_apply, ContinuousLinearMap.id_apply]
  · refine ContinuousLinearMap.ext fun T ↦ DFunLike.ext _ _ fun s ↦ ?_
    rw [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.precompCompactConvergenceCLM_apply_apply,
      ContinuousLinearMap.precompCompactConvergenceCLM_apply_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.coe_coe, e.apply_symm_apply, ContinuousLinearMap.id_apply]

/-- Universal-open distribution restriction pairs against the intrinsic test comparison. -/
@[simp]
theorem univCLE_apply (T : TauCeti.BundleDistribution I M F V)
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ)
      (openHomBundle (I := I) (V := V) (U := ⊤))) :
    univCLE (I := I) (F := F) (V := V) T s =
      T (univTestCLE (I := I) (F := F) (V := V) s) := by
  exact ContinuousLinearMap.precompCompactConvergenceCLM_apply_apply _ _ _

/-- The inverse universal-open comparison pairs against the inverse test comparison. -/
@[simp]
theorem univCLE_symm_apply
    (T : TauCeti.BundleDistribution I (⊤ : Opens M) F
      ((⟨Subtype.val, continuous_subtypeVal⟩ : C((⊤ : Opens M), M)) *ᵖ V))
    (s : TauCeti.BundleTest I (F →L[ℝ] ℝ) (ambientHomBundle (I := I) (V := V))) :
    (univCLE (I := I) (F := F) (V := V)).symm T s =
      T ((univTestCLE (I := I) (F := F) (V := V)).symm s) := by
  exact ContinuousLinearMap.precompCompactConvergenceCLM_apply_apply _ _ _

/-- The universal-open equivalence has the actual intrinsic restriction as its forward map. -/
@[simp]
theorem univCLE_toContinuousLinearMap :
    (univCLE (I := I) (F := F) (V := V)).toContinuousLinearMap =
      restrictCLM (I := I) (F := F) (V := V) (U := ⊤) := by
  apply ContinuousLinearMap.ext
  intro T
  refine DFunLike.ext _ _ fun s ↦ ?_
  rw [ContinuousLinearEquiv.coe_coe, univCLE_apply, restrictCLM_apply, testExtensionCLM_apply,
    univTestCLE, ContinuousLinearEquiv.trans_apply, ← ContinuousLinearEquiv.coe_coe,
    TauCeti.BundleTest.univCLE_toContinuousLinearMap]

end TauCeti.BundleDistribution
