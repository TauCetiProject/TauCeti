/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Tensor
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
import TauCeti.Geometry.Manifold.VectorField.LieBracket

/-!
# Curvature of a metric-compatible connection

The curvature endomorphisms of a metric-compatible connection are skew-adjoint:
`⟪R(X,Y)σ, τ⟫ = -⟪σ, R(X,Y)τ⟫`. We prove this first for smooth fields and sections,
then for the pointwise curvature tensor on arbitrary fibre vectors.

On the tangent bundle this is antisymmetry in the last two arguments of the
metric-lowered Riemann tensor. Together with antisymmetry in the first two arguments,
it makes the sectional-curvature numerator transform by the square of the determinant
under a change of basis of a tangent plane. No torsion-free hypothesis is required:
the result holds for any metric-compatible connection on a finite-rank real bundle.

The argument differentiates the metric product rule twice and uses the commutator
identity for directional derivatives to cancel the scalar second derivatives.
The metric and curvature conventions are those of J. M. Lee, *Introduction to Riemannian
Manifolds*, 2nd ed., Springer GTM 176 (2018), equation (5.1) and Chapter 7, pp. 196–198:
`R(X,Y)σ = ∇_X ∇_Y σ - ∇_Y ∇_X σ - ∇_[X,Y] σ`.
-/

public section

open Bundle FiberBundle VectorField
open scoped ContDiff Manifold

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  {cov : CovariantDerivative I F V} [ContMDiffCovariantDerivative cov ∞]

private theorem IsMetricCompatible.mvfderiv_mvfderiv_inner
    [IsContMDiffRiemannianBundle I 1 F V]
    (hcov : cov.IsMetricCompatible)
    {X Y : Π x : M, TangentSpace I x} {σ τ : Π x : M, V x}
    (hY : CMDiff ∞ (T% Y)) (hσ : CMDiff ∞ (T% σ)) (hτ : CMDiff ∞ (T% τ))
    (x : M) :
    mvfderiv I (fun y ↦ mvfderiv I (fun z ↦ inner ℝ (σ z) (τ z)) y (Y y)) x (X x) =
      inner ℝ (cov (fun y ↦ cov σ y (Y y)) x (X x)) (τ x) +
      inner ℝ (cov σ x (Y x)) (cov τ x (X x)) +
      (inner ℝ (cov σ x (X x)) (cov τ x (Y x)) +
      inner ℝ (σ x) (cov (fun y ↦ cov τ y (Y y)) x (X x))) := by
  have hYσ := cov.contMDiff_apply hY hσ
  have hYτ := cov.contMDiff_apply hY hτ
  have hmetric : (fun y ↦ mvfderiv I (fun z ↦ inner ℝ (σ z) (τ z)) y (Y y)) =
      fun y ↦ inner ℝ (cov σ y (Y y)) (τ y) + inner ℝ (σ y) (cov τ y (Y y)) := by
    funext y
    exact hcov.mvfderiv_inner_eq Y (hσ.mdifferentiable (by simp) y)
      (hτ.mdifferentiable (by simp) y)
  rw [hmetric, mvfderiv_fun_add
    (((hYσ.mdifferentiable (by simp)).inner_bundle (hτ.mdifferentiable (by simp))) x)
    (((hσ.mdifferentiable (by simp)).inner_bundle (hYτ.mdifferentiable (by simp))) x)]
  simp only [add_apply]
  rw [hcov.mvfderiv_inner_eq X (hYσ.mdifferentiable (by simp) x)
      (hτ.mdifferentiable (by simp) x),
    hcov.mvfderiv_inner_eq X (hσ.mdifferentiable (by simp) x)
      (hYτ.mdifferentiable (by simp) x)]

/-- The curvature of a smooth metric-compatible connection is skew-adjoint on smooth
sections. The base model may be infinite-dimensional, provided it is complete. -/
theorem IsMetricCompatible.inner_curvatureOperator [CompleteSpace E]
    [IsContMDiffRiemannianBundle I 2 F V]
    (hcov : cov.IsMetricCompatible)
    {X Y : Π x : M, TangentSpace I x} {σ τ : Π x : M, V x}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y))
    (hσ : CMDiff ∞ (T% σ)) (hτ : CMDiff ∞ (T% τ)) (x : M) :
    inner ℝ (cov.curvatureOperator X Y σ x) (τ x) =
      -inner ℝ (σ x) (cov.curvatureOperator X Y τ x) := by
  let _ : IsManifold I (minSmoothness ℝ 2) M :=
    IsManifold.of_le (m := minSmoothness ℝ 2) (n := ∞) (by simp)
  have hcomm := mvfderiv_mlieBracket
    ((hσ.of_le (m := 2) (by simp)).inner_bundle
      (hτ.of_le (m := 2) (by simp))).contMDiffAt (by simp)
    (hX.mdifferentiable (by simp) x) (hY.mdifferentiable (by simp) x)
  rw [hcov.mvfderiv_inner_eq (mlieBracket I X Y)
      (hσ.mdifferentiable (by simp) x) (hτ.mdifferentiable (by simp) x),
    hcov.mvfderiv_mvfderiv_inner hY hσ hτ x,
    hcov.mvfderiv_mvfderiv_inner hX hσ hτ x] at hcomm
  simp only [curvatureOperator_apply, inner_sub_left, inner_sub_right]
  linarith

/-- Every pointwise curvature endomorphism of a smooth metric-compatible connection is
skew-adjoint. For the tangent bundle, this is the last-pair antisymmetry of the Riemann
curvature tensor after lowering its output index with the metric. -/
theorem IsMetricCompatible.inner_curvatureTensor
    [IsContMDiffRiemannianBundle I 2 F V]
    [FiniteDimensional ℝ E] [T2Space M] (hcov : cov.IsMetricCompatible)
    (x : M) (u v : TangentSpace I x) (w z : V x) :
    inner ℝ (cov.curvatureTensor x u v w) z =
      -inner ℝ w (cov.curvatureTensor x u v z) := by
  obtain ⟨X, hX, rfl⟩ := exists_contMDiff_section_eq I E u
  obtain ⟨Y, hY, rfl⟩ := exists_contMDiff_section_eq I E v
  obtain ⟨σ, hσ, rfl⟩ := exists_contMDiff_section_eq I F w
  obtain ⟨τ, hτ, rfl⟩ := exists_contMDiff_section_eq I F z
  rw [curvatureTensor_apply cov x hX hY hσ, curvatureTensor_apply cov x hX hY hτ]
  exact hcov.inner_curvatureOperator hX hY hσ hτ x

end CovariantDerivative
