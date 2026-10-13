/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Trace
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Basic

/-!
# Divergence, Hessian, and Laplace–Beltrami operators

This file introduces the pointwise Riemannian divergence as the trace of the Levi–Civita
covariant derivative, the scalar Hessian obtained by pairing that derivative of the gradient,
and the Laplace–Beltrami operator with the convention `Δ = div ∘ grad`.  The orthonormal-basis
trace formula makes the relationship between the Laplacian and the Hessian explicit.

-/

noncomputable section
public section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]

/-- The Riemannian divergence of a vector field, defined as the trace of its
Levi–Civita covariant derivative. -/
noncomputable def divergence (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (X : (x : M) → TangentSpace I x) (x : M) : ℝ :=
  LinearMap.trace ℝ (TangentSpace I x)
    (CovariantDerivative.leviCivitaConnection I M X x).toLinearMap

theorem divergence_def (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (X : (x : M) → TangentSpace I x) (x : M) :
    divergence I X x =
      LinearMap.trace ℝ (TangentSpace I x)
        (CovariantDerivative.leviCivitaConnection I M X x).toLinearMap := by
  rw [divergence]

/-- The scalar Hessian of `f`, pairing the covariant derivative of its gradient with a second
tangent vector. -/
noncomputable def hessian (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (f : M → ℝ) (x : M) (v w : TangentSpace I x) : ℝ :=
  inner ℝ (CovariantDerivative.leviCivitaConnection I M (riemannianGradient I f) x v) w

theorem hessian_def (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (f : M → ℝ) (x : M) (v w : TangentSpace I x) :
    hessian I f x v w =
      inner ℝ (CovariantDerivative.leviCivitaConnection I M (riemannianGradient I f) x v) w := by
  rw [hessian]

/-- The Laplace–Beltrami operator, with the sign convention `Δ = div ∘ grad`. -/
noncomputable def laplaceBeltrami (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (f : M → ℝ) (x : M) : ℝ :=
  divergence I (riemannianGradient I f) x

theorem laplaceBeltrami_def (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (f : M → ℝ) (x : M) :
    laplaceBeltrami I f x = divergence I (riemannianGradient I f) x := by
  rw [laplaceBeltrami]

theorem divergence_eq_sum_inner (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    {m : ℕ} (X : (x : M) → TangentSpace I x) (x : M)
    (b : OrthonormalBasis (Fin m) ℝ (TangentSpace I x)) :
    divergence I X x = ∑ i, inner ℝ
      (CovariantDerivative.leviCivitaConnection I M X x (b i)) (b i) := by
  rw [divergence, LinearMap.trace_eq_sum_inner _ b]
  simp only [real_inner_comm]
  rfl

@[simp] theorem hessian_add_left (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (f : M → ℝ) (x : M) (v₁ v₂ w : TangentSpace I x) :
    hessian I f x (v₁ + v₂) w = hessian I f x v₁ w + hessian I f x v₂ w := by
  simp only [hessian, map_add, inner_add_left]

@[simp] theorem hessian_smul_left (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (f : M → ℝ) (x : M) (r : ℝ) (v w : TangentSpace I x) :
    hessian I f x (r • v) w = r * hessian I f x v w := by
  simp only [hessian, map_smul, real_inner_smul_left]

@[simp] theorem hessian_zero_left (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (f : M → ℝ) (x : M) (w : TangentSpace I x) :
    hessian I f x 0 w = 0 := by
  simp only [hessian, map_zero, inner_zero_left]

@[simp] theorem hessian_add_right (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (f : M → ℝ) (x : M) (v w₁ w₂ : TangentSpace I x) :
    hessian I f x v (w₁ + w₂) = hessian I f x v w₁ + hessian I f x v w₂ := by
  simp only [hessian, inner_add_right]

@[simp] theorem hessian_smul_right (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (f : M → ℝ) (x : M) (r : ℝ) (v w : TangentSpace I x) :
    hessian I f x v (r • w) = r * hessian I f x v w := by
  simp only [hessian, real_inner_smul_right]

@[simp] theorem hessian_zero_right (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M]
    [IsManifold I 1 M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (f : M → ℝ) (x : M) (v : TangentSpace I x) :
    hessian I f x v 0 = 0 := by
  simp only [hessian, inner_zero_right]

/-- The Laplace–Beltrami operator is the trace of the scalar Hessian in every orthonormal basis. -/
theorem laplaceBeltrami_eq_sum_hessian (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    {m : ℕ} (f : M → ℝ) (x : M)
    (b : OrthonormalBasis (Fin m) ℝ (TangentSpace I x)) :
    laplaceBeltrami I f x = ∑ i, hessian I f x (b i) (b i) := by
  rw [laplaceBeltrami, divergence, LinearMap.trace_eq_sum_inner _ b]
  simp only [hessian, real_inner_comm]
  rfl

end TauCeti.Manifold
