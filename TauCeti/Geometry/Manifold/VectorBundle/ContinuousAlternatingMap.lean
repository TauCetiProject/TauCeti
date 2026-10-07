/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.ContinuousAlternatingMap
public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
public import TauCeti.Analysis.Calculus.ContDiff.ContinuousAlternatingMap

/-!
# Smooth bundles of continuous alternating maps

Continuous alternating maps between the fibers of two `C^n` vector bundles form a `C^n`
vector bundle when the degree factorial is nonzero in the scalar field, in particular over `ℝ`.
The fibers can be infinite dimensional, and the base can have boundary or corners.
This supplies the smooth bundle in which bundle-valued differential forms are sections.

We retain Mathlib's topology, atlas and coordinate representation. A map into the total space
is smooth exactly when its base map and its alternating-map coefficients in local coordinates
are smooth. The construction follows Mathlib's `Geometry.Manifold.VectorBundle.Hom`, by
Floris van Doorn, and the topological alternating-map bundle by Yury Kudryashov, Heather Macbeth
and Floris van Doorn.

The coordinate regularity criteria do not require the factorial hypothesis.
-/

public noncomputable section

open Bundle Set
open scoped Manifold Bundle Topology ContDiff

namespace TauCeti

variable {𝕜 ι B F₁ F₂ : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]
  [NeZero ((Fintype.card ι).factorial : 𝕜)]
  {n : ℕ∞ω} {E₁ : B → Type*} {E₂ : B → Type*}
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  [TopologicalSpace B] [ChartedSpace HB B]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

/-- The coordinate changes of the alternating-map bundle are `C^n` on chart overlaps. -/
theorem contMDiffOn_continuousAlternatingMapCoordChange
    [ContMDiffVectorBundle n F₁ E₁ IB] [ContMDiffVectorBundle n F₂ E₂ IB]
    (e₁ e₁' : Trivialization F₁ (π F₁ E₁)) (e₂ e₂' : Trivialization F₂ (π F₂ E₂))
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₁']
    [MemTrivializationAtlas e₂] [MemTrivializationAtlas e₂'] :
    ContMDiffOn IB 𝓘(𝕜, (F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] F₁ [⋀^ι]→L[𝕜] F₂) n
      (Pretrivialization.continuousAlternatingMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂')
      (e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) := by
  simp +unfoldPartialApp only [Pretrivialization.continuousAlternatingMapCoordChange,
    ContinuousLinearEquiv.coe_continuousAlternatingMapCongr, ContinuousLinearEquiv.symm_symm]
  refine .clm_comp ?_ ?_
  · let L : (F₂ →L[𝕜] F₂) →L[𝕜]
        (F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] F₁ [⋀^ι]→L[𝕜] F₂ :=
      ContinuousLinearMap.compContinuousAlternatingMapCLM 𝕜 F₁ F₂ F₂ ι
    refine (ContinuousLinearMap.contDiff (𝕜 := 𝕜) (E := F₂ →L[𝕜] F₂)
      (F := (F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] F₁ [⋀^ι]→L[𝕜] F₂) L).contMDiff.comp_contMDiffOn
      ((contMDiffOn_coordChangeL (IB := IB) e₂ e₂' (n := n)).mono ?_)
    mfld_set_tac
  · refine contDiff_compContinuousLinearMapCLM.contMDiff.comp_contMDiffOn
      ((contMDiffOn_coordChangeL (IB := IB) e₁' e₁ (n := n)).mono ?_)
    mfld_set_tac

variable [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]

/-- Smoothness of the existing alternating-map prebundle, using its existing coordinate changes. -/
instance instIsContMDiffContinuousAlternatingMapVectorPrebundle
    [ContMDiffVectorBundle n F₁ E₁ IB] [ContMDiffVectorBundle n F₂ E₂ IB] :
    (Bundle.ContinuousAlternatingMap.vectorPrebundle 𝕜 ι F₁ E₁ F₂ E₂).IsContMDiff IB n where
  exists_contMDiffCoordChange := by
    rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩ _ ⟨e₁', e₂', he₁', he₂', rfl⟩
    exact ⟨Pretrivialization.continuousAlternatingMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂',
      contMDiffOn_continuousAlternatingMapCoordChange e₁ e₁' e₂ e₂',
      Pretrivialization.continuousAlternatingMapCoordChange_apply⟩

/-- Alternating maps between fibers of `C^n` vector bundles form a `C^n` vector bundle. -/
instance instContMDiffVectorBundleContinuousAlternatingMap
    [ContMDiffVectorBundle n F₁ E₁ IB] [ContMDiffVectorBundle n F₂ E₂ IB] :
    ContMDiffVectorBundle n (F₁ [⋀^ι]→L[𝕜] F₂) (fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x) IB :=
  (Bundle.ContinuousAlternatingMap.vectorPrebundle 𝕜 ι F₁ E₁ F₂ E₂).contMDiffVectorBundle IB

section Coordinates

variable {M EM HM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  [TopologicalSpace HM] {IM : ModelWithCorners 𝕜 EM HM}
  [TopologicalSpace M] [ChartedSpace HM M] {s : Set M} {x₀ : M}

omit [NeZero ((Fintype.card ι).factorial : 𝕜)] in
/-- Smoothness within a set in the alternating-map bundle is smoothness of the base map
and of the alternating map written in the preferred fiber coordinates. -/
theorem contMDiffWithinAt_continuousAlternatingMap_bundle
    (f : M → TotalSpace (F₁ [⋀^ι]→L[𝕜] F₂) (fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x)) :
    ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F₁ [⋀^ι]→L[𝕜] F₂)) n f s x₀ ↔
      ContMDiffWithinAt IM IB n (fun x ↦ (f x).1) s x₀ ∧
        ContMDiffWithinAt IM 𝓘(𝕜, F₁ [⋀^ι]→L[𝕜] F₂) n
          (fun x ↦ ContinuousAlternatingMap.inCoordinates F₁ F₂
            (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) s x₀ :=
  contMDiffWithinAt_totalSpace

omit [NeZero ((Fintype.card ι).factorial : 𝕜)] in
/-- Smoothness at a point in the alternating-map bundle is smoothness of the base map
and of its coefficients in preferred fiber coordinates. -/
theorem contMDiffAt_continuousAlternatingMap_bundle
    (f : M → TotalSpace (F₁ [⋀^ι]→L[𝕜] F₂) (fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x)) :
    ContMDiffAt IM (IB.prod 𝓘(𝕜, F₁ [⋀^ι]→L[𝕜] F₂)) n f x₀ ↔
      ContMDiffAt IM IB n (fun x ↦ (f x).1) x₀ ∧
        ContMDiffAt IM 𝓘(𝕜, F₁ [⋀^ι]→L[𝕜] F₂) n
          (fun x ↦ ContinuousAlternatingMap.inCoordinates F₁ F₂
            (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) x₀ :=
  contMDiffAt_totalSpace

omit [NeZero ((Fintype.card ι).factorial : 𝕜)] in
/-- Differentiability within a set in the alternating-map bundle is differentiability of the
base map and of the alternating map written in the preferred fiber coordinates. -/
theorem mdifferentiableWithinAt_continuousAlternatingMap_bundle
    (f : M → TotalSpace (F₁ [⋀^ι]→L[𝕜] F₂) (fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x)) :
    MDifferentiableWithinAt IM (IB.prod 𝓘(𝕜, F₁ [⋀^ι]→L[𝕜] F₂)) f s x₀ ↔
      MDifferentiableWithinAt IM IB (fun x ↦ (f x).1) s x₀ ∧
        MDifferentiableWithinAt IM 𝓘(𝕜, F₁ [⋀^ι]→L[𝕜] F₂)
          (fun x ↦ ContinuousAlternatingMap.inCoordinates F₁ F₂
            (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) s x₀ :=
  mdifferentiableWithinAt_totalSpace IB ..

omit [NeZero ((Fintype.card ι).factorial : 𝕜)] in
/-- Differentiability at a point in the alternating-map bundle is differentiability of the
base map and of its coefficients in preferred fiber coordinates. -/
theorem mdifferentiableAt_continuousAlternatingMap_bundle
    (f : M → TotalSpace (F₁ [⋀^ι]→L[𝕜] F₂) (fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x)) :
    MDifferentiableAt IM (IB.prod 𝓘(𝕜, F₁ [⋀^ι]→L[𝕜] F₂)) f x₀ ↔
      MDifferentiableAt IM IB (fun x ↦ (f x).1) x₀ ∧
        MDifferentiableAt IM 𝓘(𝕜, F₁ [⋀^ι]→L[𝕜] F₂)
          (fun x ↦ ContinuousAlternatingMap.inCoordinates F₁ F₂
            (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) x₀ :=
  mdifferentiableAt_totalSpace ..

end Coordinates

end TauCeti
