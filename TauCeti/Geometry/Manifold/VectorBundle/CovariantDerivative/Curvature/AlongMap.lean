/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Smoothness
import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
# Curvature evaluation along maps

The curvature of a smooth connection evaluates smoothly on tangent fields and a bundle
section along any smooth map, including within an arbitrary parameter set. The fields may
have finite differentiability even though the connection is smooth. No metric compatibility
or torsion assumption is required.

The tensor is `CovariantDerivative.curvatureTensor`; the proof evaluates its smooth
hom-bundle representation `CovariantDerivative.curvatureTensorCLM`.
-/

public section

open Bundle
open scoped ContDiff Manifold

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [fiberNorm : ∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  (cov : CovariantDerivative I F V) [ContMDiffCovariantDerivative cov ∞]

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H' P]
  {f : P → M} {X Y : Π p : P, TangentSpace I (f p)} {σ : Π p : P, V (f p)}
  {s : Set P} {p : P} {n : ℕ∞ω}

/-- Curvature evaluates smoothly on fields along a map, within any parameter set.
The connection may be on any finite-dimensional smooth vector bundle. -/
theorem contMDiffWithinAt_curvatureTensor_alongMap
    (hf : ContMDiffWithinAt I' I n f s p)
    (hX : ContMDiffWithinAt I' I.tangent n
      (fun q ↦ TotalSpace.mk' E (f q) (X q)) s p)
    (hY : ContMDiffWithinAt I' I.tangent n
      (fun q ↦ TotalSpace.mk' E (f q) (Y q)) s p)
    (hσ : ContMDiffWithinAt I' (I.prod 𝓘(ℝ, F)) n
      (fun q ↦ TotalSpace.mk' F (f q) (σ q)) s p) (hn : n ≤ ∞) :
    ContMDiffWithinAt I' (I.prod 𝓘(ℝ, F)) n
      (fun q ↦ TotalSpace.mk' F (f q)
        (cov.curvatureTensor (f q) (X q) (Y q) (σ q))) s p := by
  let _ : NormedAddCommGroup (F →L[ℝ] F) := inferInstance
  let _ : NormedSpace ℝ (F →L[ℝ] F) := inferInstance
  let _ : ∀ x : M, NormedAddCommGroup (V x →L[ℝ] V x) := fun _ ↦ inferInstance
  let _ : ∀ x : M, NormedSpace ℝ (V x →L[ℝ] V x) := fun _ ↦ inferInstance
  have hR := (cov.contMDiff_curvatureTensorCLM.of_le hn).contMDiffAt.comp_contMDiffWithinAt
    p hf
  simpa only [curvatureTensorCLM_apply] using
    ((hR.clm_bundle_apply hX).clm_bundle_apply hY).clm_bundle_apply hσ

end CovariantDerivative
