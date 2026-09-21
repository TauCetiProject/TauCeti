/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Tensor
import TauCeti.Geometry.Manifold.VectorBundle.Hom

/-!
# Smoothness of the curvature tensor

The pointwise curvature tensor of a smooth connection is a smooth section of the
iterated hom bundle. We express the existing algebraic `curvatureTensor` using
continuous linear maps, so Mathlib's hom-bundle topology and smooth structure apply.
The application equation identifies the two tensors, without any new choice of extensions.

This smooth tensor-field packaging makes curvature available for subsequent geometric
constructions, including Ricci and sectional curvature, while retaining the original
pointwise tensor as its evaluation. It requires neither metric compatibility nor
vanishing torsion.

The curvature convention follows J. M. Lee, *Introduction to Riemannian Manifolds*,
2nd ed., Springer GTM 176 (2018), Chapter 7, pp. 196–198, as in `curvatureTensor`.
-/

public section

open Bundle
open scoped ContDiff Manifold

noncomputable section

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

/-- The curvature tensor as an iterated continuous linear map, in the fibre of the
iterated hom bundle. Its underlying trilinear map is `curvatureTensor`. -/
def curvatureTensorCLM (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] V x →L[ℝ] V x :=
  haveI := VectorBundle.finiteDimensional ℝ F V x
  LinearMap.toContinuousLinearMap
    (LinearMap.toContinuousLinearMap.toLinearMap.comp
      ((cov.curvatureTensor x).compr₂ LinearMap.toContinuousLinearMap.toLinearMap))

/-- The continuous-linear curvature tensor evaluates to the original pointwise tensor. -/
@[simp]
theorem curvatureTensorCLM_apply (x : M) (u v : TangentSpace I x) (w : V x) :
    cov.curvatureTensorCLM x u v w = cov.curvatureTensor x u v w := by
  simp only [curvatureTensorCLM, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_comp,
    LinearEquiv.coe_coe, Function.comp_apply, LinearMap.compr₂_apply]

/-- The curvature tensor of a smooth connection is a smooth section of the iterated
hom bundle. This requires neither metric compatibility nor vanishing torsion. -/
theorem contMDiff_curvatureTensorCLM :
    -- Cache the standard model instances while elaborating the nested operator spaces.
    let _ : NormedAddCommGroup (F →L[ℝ] F) := inferInstance
    let _ : NormedSpace ℝ (F →L[ℝ] F) := inferInstance
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] F →L[ℝ] F)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] F →L[ℝ] F) x
        (cov.curvatureTensorCLM x)) := by
  intro normEnd spaceEnd
  apply (TauCeti.Manifold.contMDiff_hom_iff _).2
  intro X hX
  apply (TauCeti.Manifold.contMDiff_hom_iff _).2
  intro Y hY
  apply (TauCeti.Manifold.contMDiff_hom_iff _).2
  intro σ hσ
  simpa only [curvatureTensorCLM_apply, curvatureTensor_apply cov _ hX hY hσ] using
    cov.contMDiff_curvatureOperator hX hY hσ

end CovariantDerivative
