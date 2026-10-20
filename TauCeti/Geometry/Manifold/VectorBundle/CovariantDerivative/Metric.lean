/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity

/-!
# Higher metric product rules

This module records the twice-differentiated product rule for a metric-compatible covariant
derivative. It supplies the second-derivative calculation used to establish curvature
skew-adjointness and can be reused in other calculations with metric-compatible connections.

It also restates metric compatibility with a bundled metric `g`, installed as the
`RiemannianBundle` instance, in terms of the inner products of `g`
(`Bundle.ContMDiffRiemannianMetric.isMetricCompatible_iff_inner`). This is the form in which
connections are compared across different metrics on the same bundle.
-/

public section

open Bundle FiberBundle
open scoped ContDiff Manifold

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle 1 F V I] [IsContMDiffRiemannianBundle I 1 F V]
  {n : ℕ∞ω} {cov : CovariantDerivative I F V} [ContMDiffCovariantDerivative cov n]

/-- The twice-differentiated metric product rule for a `C^n` metric-compatible connection. -/
theorem IsMetricCompatible.mvfderiv_mvfderiv_inner
    (hcov : cov.IsMetricCompatible)
    {X Y : Π x : M, TangentSpace I x} {σ τ : Π x : M, V x}
    (hn : 1 ≤ n) (hY : CMDiff n (T% Y))
    (hσ : CMDiff (n + 1) (T% σ)) (hτ : CMDiff (n + 1) (T% τ))
    (x : M) :
    mvfderiv I (fun y ↦ mvfderiv I (fun z ↦ inner ℝ (σ z) (τ z)) y (Y y)) x (X x) =
      inner ℝ (cov (fun y ↦ cov σ y (Y y)) x (X x)) (τ x) +
      inner ℝ (cov σ x (Y x)) (cov τ x (X x)) +
      (inner ℝ (cov σ x (X x)) (cov τ x (Y x)) +
      inner ℝ (σ x) (cov (fun y ↦ cov τ y (Y y)) x (X x))) := by
  have hn0 : n ≠ 0 := ne_of_gt (lt_of_lt_of_le (by simp) hn)
  have hYσ := cov.contMDiff_apply hY hσ
  have hYτ := cov.contMDiff_apply hY hτ
  have hmetric : (fun y ↦ mvfderiv I (fun z ↦ inner ℝ (σ z) (τ z)) y (Y y)) =
      fun y ↦ inner ℝ (cov σ y (Y y)) (τ y) + inner ℝ (σ y) (cov τ y (Y y)) := by
    funext y
    exact hcov.mvfderiv_inner_eq Y (hσ.mdifferentiable (by simp) y)
      (hτ.mdifferentiable (by simp) y)
  rw [hmetric, mvfderiv_fun_add
    (((hYσ.mdifferentiable hn0).inner_bundle (hτ.mdifferentiable (by simp))) x)
    (((hσ.mdifferentiable (by simp)).inner_bundle (hYτ.mdifferentiable hn0)) x)]
  simp only [add_apply]
  rw [hcov.mvfderiv_inner_eq X (hYσ.mdifferentiable hn0 x)
      (hτ.mdifferentiable (by simp) x),
    hcov.mvfderiv_inner_eq X (hσ.mdifferentiable (by simp) x)
      (hYτ.mdifferentiable hn0 x)]

end CovariantDerivative

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I] {n : ℕ∞ω}

/-- Metric compatibility with a `C¹` bundled metric `g`, installed as the `RiemannianBundle`
instance, written with the inner products of `g`. -/
theorem isMetricCompatible_iff_inner (g : ContMDiffRiemannianMetric I n F V) (hn : 1 ≤ n)
    (cov : CovariantDerivative I F V) :
    (letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 F V := IsContMDiffRiemannianBundle.of_le hn;
      cov.IsMetricCompatible) ↔
      ∀ ⦃x : M⦄ ⦃X : Π x : M, TangentSpace I x⦄ ⦃σ τ : Π x : M, V x⦄,
        MDiffAt (T% X) x → MDiffAt (T% σ) x → MDiffAt (T% τ) x →
        mvfderiv I (fun y ↦ g.inner y (σ y) (τ y)) x (X x) =
          g.inner x (cov σ x (X x)) (τ x) + g.inner x (σ x) (cov τ x (X x)) := by
  let _ : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle I 1 F V := IsContMDiffRiemannianBundle.of_le hn
  simp only [CovariantDerivative.isMetricCompatible_iff, inner_riemannianBundle]

end Bundle.ContMDiffRiemannianMetric
