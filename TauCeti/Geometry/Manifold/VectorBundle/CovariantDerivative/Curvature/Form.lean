/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Curvature
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Smoothness
import TauCeti.Geometry.Manifold.VectorBundle.ContinuousAlternatingMap
import TauCeti.LinearAlgebra.BilinearMap.Multilinear
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# The endomorphism-valued curvature two-form

The curvature of a smooth connection is a smooth two-form with values in the native
endomorphism bundle. `CovariantDerivative.curvatureForm` packages the existing curvature
tensor in `TauCeti.CurvatureForm`, without choosing a frame or changing its normalization.
Its value on `X, Y`, applied to a section `σ`, is
`∇_X ∇_Y σ - ∇_Y ∇_X σ - ∇_[X,Y] σ`.

This identifies the tensor used for pointwise curvature computations with the differential
form used in structure equations and exterior covariant differentiation. No metric or
torsion assumption is required.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 7.
* The construction uses `CovariantDerivative.curvatureTensorCLM` and its smoothness theorem;
  the alternating-map and endomorphism bundles have their existing Mathlib topologies.
-/

public section

open Bundle FiberBundle
open scoped ContDiff Manifold Topology

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  (cov : CovariantDerivative I F V) [ContMDiffCovariantDerivative cov ∞]

private def curvatureAlternatingMap (x : M) :
    TangentSpace I x [⋀^Fin 2]→L[ℝ] (V x →L[ℝ] V x) :=
  haveI := VectorBundle.finiteDimensional ℝ F V x
  AlternatingMap.toContinuousAlternatingMap
    (LinearMap.IsAlt.toAlternatingMap
      -- Retain the named predicate when elaborating the alternating-map constructor.
      (show ((cov.curvatureTensor x).compr₂
        LinearMap.toContinuousLinearMap.toLinearMap).IsAlt from fun u ↦ by simp))

private theorem curvatureAlternatingMap_apply (x : M) (v : Fin 2 → TangentSpace I x) :
    cov.curvatureAlternatingMap x v = cov.curvatureTensorCLM x (v 0) (v 1) := by
  ext w
  rw [curvatureAlternatingMap, AlternatingMap.coe_toContinuousAlternatingMap,
    LinearMap.IsAlt.toAlternatingMap_apply]
  simp only [LinearMap.compr₂_apply, LinearEquiv.coe_coe, LinearMap.coe_toContinuousLinearMap',
    curvatureTensorCLM_apply]

private theorem contMDiff_curvatureAlternatingMap :
    ContMDiff I (I.prod 𝓘(ℝ, E [⋀^Fin 2]→L[ℝ] (F →L[ℝ] F))) ∞
      (fun x ↦ TotalSpace.mk' (E [⋀^Fin 2]→L[ℝ] (F →L[ℝ] F)) x
        (cov.curvatureAlternatingMap x)) :=
  fun x ↦ TauCeti.contMDiffAt_continuousAlternatingMap_bundle_of_bilinear
    (cov.contMDiff_curvatureTensorCLM x) cov.curvatureAlternatingMap_apply

/-- The curvature of a smooth connection as a smooth endomorphism-valued two-form.
Its evaluation is `R(X,Y)`, with no additional factor of two. -/
def curvatureForm : TauCeti.CurvatureForm I F V :=
  ⟨cov.curvatureAlternatingMap, TauCeti.mem_smoothBundleForms.mpr
    (TauCeti.isSmoothBundleForm_def ∞ _ |>.mpr cov.contMDiff_curvatureAlternatingMap)⟩

/-- The curvature form evaluates to the existing pointwise curvature tensor. -/
@[simp]
theorem curvatureForm_apply (x : M) (v : Fin 2 → TangentSpace I x) (w : V x) :
    cov.curvatureForm.val x v w = cov.curvatureTensor x (v 0) (v 1) w := by
  rw [curvatureForm, curvatureAlternatingMap_apply, curvatureTensorCLM_apply]

/-- On smooth fields and sections, the curvature form is the commutator of covariant
derivatives corrected by the Lie bracket. -/
theorem curvatureForm_eval₂_eq_curvatureOperator (x : M)
    {X Y : Π y : M, TangentSpace I y} {σ : Π y : M, V y}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hσ : CMDiff ∞ (T% σ)) :
    cov.curvatureForm.eval₂ x (X x) (Y x) (σ x) = curvatureOperator cov X Y σ x := by
  simpa using cov.curvatureTensor_apply x hX hY hσ

/-- The curvature form is uniquely determined by its curvature-tensor evaluations. -/
theorem curvatureForm_eq_iff (Ω : TauCeti.CurvatureForm I F V) :
    cov.curvatureForm = Ω ↔ ∀ x (u v : TangentSpace I x) (w : V x),
      Ω.eval₂ x u v w = cov.curvatureTensor x u v w := by
  constructor
  · rintro rfl x u v w
    simp
  · intro h
    apply TauCeti.SmoothBundleForm.ext_eval₂
    intro x u v
    ext w
    simpa using (h x u v w).symm

/-- Vanishing of the curvature form is equivalent to vanishing of the pointwise tensor. -/
@[simp]
theorem curvatureForm_eq_zero_iff :
    cov.curvatureForm = 0 ↔ ∀ x, cov.curvatureTensor x = 0 := by
  rw [curvatureForm_eq_iff]
  constructor
  · intro h x
    ext u v w
    simpa using (h x u v w).symm
  · intro h x u v w
    simp [h x]

end CovariantDerivative
