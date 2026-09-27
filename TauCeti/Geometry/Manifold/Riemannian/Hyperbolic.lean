/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Tensor

/-!
# Hyperbolic metrics

This file packages the data used by a hyperbolic structure: a smooth Riemannian metric, metric
completeness, and the standard constant-curvature tensor with parameter `-1` (the tensor form of
constant sectional curvature). The metric is bundled so that later volume and Mostow statements
can quantify over a chosen metric; an existence predicate is deferred until a concrete model is
available.

The curvature convention follows Lee, *Introduction to Riemannian Manifolds*, 2nd edition,
Chapter 7.

The curvature predicate is stated for an arbitrary connection and then specialized to the
Levi-Civita connection of a bundled metric. This keeps the curvature equation explicit and makes
the convention visible: `R(w,u)v = κ (⟪u,v⟫ w - ⟪w,v⟫ u)`.
-/

public section

open Bundle
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [MetricSpace M]
  [IsManifold I ∞ M] [T2Space (TangentBundle I M)]

/-- A connection has constant sectional-curvature tensor `κ` when
`R(w,u)v = κ (⟪u,v⟫ w - ⟪w,v⟫ u)` at every point. -/
def IsConstantCurvatureTensor
    (g : RiemannianMetric (fun x : M ↦ TangentSpace I x))
    (cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞) (κ : ℝ) : Prop :=
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g⟩
  letI := hcov
  ∀ (x : M) (w u v : TangentSpace I x),
    cov.curvatureTensor x w u v = κ • (inner ℝ u v • w - inner ℝ w v • u)

/-- The metric `g` induces the Riemannian distance on `M` through the ambient metric space. -/
def IsRiemannianMetric
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) : Prop :=
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  IsRiemannianManifold I M

/-- The Levi-Civita connection of `g` has constant curvature `κ`. -/
def IsConstantCurvatureTensorMetric
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (κ : ℝ) : Prop :=
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  IsConstantCurvatureTensor g.toRiemannianMetric
    (CovariantDerivative.leviCivitaConnection I M) inferInstance κ

/-- A complete smooth Riemannian metric of constant curvature `-1` on `M`. -/
structure HyperbolicMetric where
  /-- The smooth Riemannian metric. -/
  metric : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)
  /-- The metric induces the ambient Riemannian distance. -/
  isRiemannian : IsRiemannianMetric (I := I) (M := M) metric
  /-- The Riemannian distance is metrically complete. -/
  complete : CompleteSpace M
  /-- The Levi-Civita connection has the constant-curvature tensor with parameter `-1`. -/
  curvature : IsConstantCurvatureTensorMetric (I := I) (M := M) metric (-1)

namespace HyperbolicMetric

omit [T2Space (TangentBundle I M)] in
/-- The curvature equation carried by a hyperbolic metric, evaluated at one tangent triple. -/
theorem curvatureTensor_eq (g : HyperbolicMetric (I := I) (M := M))
    (x : M) (w u v : TangentSpace I x) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨g.metric.toRiemannianMetric⟩
    (CovariantDerivative.leviCivitaConnection I M).curvatureTensor x w u v =
      (-1 : ℝ) • (inner ℝ u v • w - inner ℝ w v • u) := by
  have h := g.curvature
  simpa only [IsConstantCurvatureTensorMetric, IsConstantCurvatureTensor] using (h x w u v)

end HyperbolicMetric

end TauCeti
