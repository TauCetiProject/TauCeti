/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Derivative.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-!
# Smoothness of the covariant derivative of curvature

For smooth connections on a finite-rank bundle and on the tangent bundle, the covariant
derivative of curvature is a smooth tensor field. We equip the existing algebraic tensor
`CovariantDerivative.derivCurvatureTensor` with its iterated continuous-linear-map structure,
using Mathlib's hom bundles. Its evaluation is unchanged.

This supplies the regularity of the tensor appearing in cubic normal-coordinate expansions
and permits differentiating its components in smooth local frames. Neither metric compatibility
nor vanishing torsion is required; the two connections may be different.

## Main results

* `CovariantDerivative.derivCurvatureTensorCLM`: the continuous-linear form of `∇R`.
* `CovariantDerivative.derivCurvatureTensorCLM_apply`: its evaluation on fibre vectors.
* `CovariantDerivative.contMDiff_derivCurvatureTensorCLM`: smoothness as a hom-bundle section.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 7 (covariant derivatives of curvature).
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
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  (cov : CovariantDerivative I F V) [ContMDiffCovariantDerivative cov ∞]
  (covT : CovariantDerivative I E (TangentSpace I : M → Type _))

/-- The covariant derivative of curvature as an iterated continuous linear map. The first
argument is the differentiation direction, followed by the two curvature directions and
the bundle vector, as for `derivCurvatureTensor`. -/
def derivCurvatureTensorCLM (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] V x →L[ℝ] V x :=
  haveI := VectorBundle.finiteDimensional ℝ F V x
  haveI := FiberBundle.t2Space F V x
  let e₁ : (V x →ₗ[ℝ] V x) ≃ₗ[ℝ] (V x →L[ℝ] V x) :=
    LinearMap.toContinuousLinearMap
  let e₂ : (TangentSpace I x →ₗ[ℝ] V x →ₗ[ℝ] V x) ≃ₗ[ℝ]
      (TangentSpace I x →L[ℝ] V x →L[ℝ] V x) :=
    e₁.congrRight.trans LinearMap.toContinuousLinearMap
  let e₃ : (TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] V x →ₗ[ℝ] V x) ≃ₗ[ℝ]
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] V x →L[ℝ] V x) :=
    e₂.congrRight.trans LinearMap.toContinuousLinearMap
  LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := TangentSpace I x)
    (F' := TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] V x →L[ℝ] V x)
    (e₃.congrRight (cov.derivCurvatureTensor covT x))

/-- The continuous-linear covariant curvature derivative evaluates to the existing algebraic
tensor, with no choice of frame or extensions. -/
@[simp]
theorem derivCurvatureTensorCLM_apply (x : M) (v u w : TangentSpace I x) (z : V x) :
    cov.derivCurvatureTensorCLM covT x v u w z = cov.derivCurvatureTensor covT x v u w z := by
  simp [derivCurvatureTensorCLM, LinearEquiv.congrRight, LinearEquiv.arrowCongr_apply]

/-- The covariant derivative of curvature of a smooth connection, taken with a smooth tangent
connection, is a smooth section of the iterated hom bundle. -/
theorem contMDiff_derivCurvatureTensorCLM [ContMDiffCovariantDerivative covT ∞] :
    -- Cache the canonical operator norms before elaborating the iterated hom bundle.
    let _ : NormedAddCommGroup (F →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
    let _ : NormedSpace ℝ (F →L[ℝ] F) := ContinuousLinearMap.toNormedSpace
    let _ : NormedAddCommGroup (E →L[ℝ] F →L[ℝ] F) :=
      ContinuousLinearMap.toNormedAddCommGroup
    let _ : NormedSpace ℝ (E →L[ℝ] F →L[ℝ] F) := ContinuousLinearMap.toNormedSpace
    let _ : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F →L[ℝ] F) :=
      ContinuousLinearMap.toNormedAddCommGroup
    let _ : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F →L[ℝ] F) := ContinuousLinearMap.toNormedSpace
    let _ : ∀ x : M, AddCommGroup (V x →L[ℝ] V x) := fun _ ↦ inferInstance
    let _ : ∀ x : M, Module ℝ (V x →L[ℝ] V x) := fun _ ↦ inferInstance
    let _ : ∀ x : M, AddCommGroup (TangentSpace I x →L[ℝ] V x →L[ℝ] V x) :=
      fun _ ↦ inferInstance
    let _ : ∀ x : M, Module ℝ (TangentSpace I x →L[ℝ] V x →L[ℝ] V x) :=
      fun _ ↦ inferInstance
    let _ : ∀ x : M, AddCommGroup
        (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] V x →L[ℝ] V x) :=
      fun _ ↦ inferInstance
    let _ : ∀ x : M, Module ℝ
        (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] V x →L[ℝ] V x) :=
      fun _ ↦ inferInstance
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E →L[ℝ] F →L[ℝ] F)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E →L[ℝ] F →L[ℝ] F) x
        (cov.derivCurvatureTensorCLM covT x)) := by
  intro normEnd spaceEnd normHom spaceHom normTensor spaceTensor addEnd moduleEnd addHom
    moduleHom addTensor moduleTensor
  apply (TauCeti.Manifold.contMDiff_hom_iff _).2
  intro X hX
  apply (TauCeti.Manifold.contMDiff_hom_iff _).2
  intro Y hY
  apply (TauCeti.Manifold.contMDiff_hom_iff _).2
  intro Z hZ
  apply (TauCeti.Manifold.contMDiff_hom_iff _).2
  intro σ hσ
  have hfirst := cov.contMDiff_apply hX (cov.contMDiff_curvatureOperator hY hZ hσ)
  have hsecond := cov.contMDiff_curvatureOperator (covT.contMDiff_apply hX hY) hZ hσ
  have hthird := cov.contMDiff_curvatureOperator hY (covT.contMDiff_apply hX hZ) hσ
  have hfourth := cov.contMDiff_curvatureOperator hY hZ (cov.contMDiff_apply hX hσ)
  simpa only [derivCurvatureTensorCLM_apply, Pi.sub_apply,
    derivCurvatureTensor_apply_eq_curvatureOperator cov covT _ hX hY hZ hσ] using
    ((hfirst.sub_section hsecond).sub_section hthird).sub_section hfourth

end CovariantDerivative
