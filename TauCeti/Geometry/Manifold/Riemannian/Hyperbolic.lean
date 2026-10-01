/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Metric
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Scalar
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Sectional

/-!
# Hyperbolic metrics

This file packages the data used by a hyperbolic structure: a smooth Riemannian metric, metric
completeness, and the standard constant-curvature tensor with parameter `-1` (the tensor form of
constant curvature). The metric is bundled so that later volume and Mostow statements
can quantify over a chosen metric.

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

namespace TauCeti

/-- A complete smooth Riemannian metric of constant curvature `-1` on `M`. -/
@[ext]
structure HyperbolicMetric where
  /-- The smooth Riemannian metric. -/
  metric : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)
  /-- The metric induces the ambient Riemannian distance. -/
  inducesRiemannianDistance : metric.InducesRiemannianDistance (I := I) (M := M)
  /-- The Riemannian distance is metrically complete. -/
  complete : CompleteSpace M
  /-- The Levi-Civita connection has the constant-curvature tensor with parameter `-1`. -/
  curvature : Bundle.ContMDiffRiemannianMetric.IsConstantCurvatureTensor
    (I := I) (M := M) metric (-1)

/-- A manifold is hyperbolic when it admits a complete smooth metric of constant curvature `-1`.

This is the existence predicate used by later hyperbolic-volume and Mostow-rigidity statements;
the chosen metric remains available through `HyperbolicMetric` when a proof is needed. -/
def IsHyperbolic : Prop := Nonempty (HyperbolicMetric (I := I) (M := M))

namespace HyperbolicMetric

/-- The curvature equation carried by a hyperbolic metric, evaluated at one tangent triple. -/
@[simp]
theorem curvatureTensor_eq (g : HyperbolicMetric (I := I) (M := M))
    (x : M) (w u v : TangentSpace I x) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨g.metric.toRiemannianMetric⟩
    (CovariantDerivative.leviCivitaConnection I M).curvatureTensor x w u v =
      (-1 : ℝ) • (inner ℝ u v • w - inner ℝ w v • u) := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨g.metric.toRiemannianMetric⟩
  exact Bundle.ContMDiffRiemannianMetric.IsConstantCurvatureTensor.curvatureTensor_eq
    g.metric (-1) g.curvature x w u v

/-- A hyperbolic metric has constant sectional curvature `-1`. -/
theorem hasConstantSectionalCurvature (g : HyperbolicMetric (I := I) (M := M)) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨g.metric.toRiemannianMetric⟩
    (CovariantDerivative.leviCivitaConnection I M).HasConstantSectionalCurvature
      (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) (-1) := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨g.metric.toRiemannianMetric⟩
  apply CovariantDerivative.hasConstantSectionalCurvature_of_curvatureTensor_eq_smul_inner_sub
    (CovariantDerivative.leviCivitaConnection I M)
    (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) (-1)
  intro x w u v
  exact g.curvatureTensor_eq x w u v

end HyperbolicMetric

/-- An `IsHyperbolic` witness has scalar curvature
`n (n - 1) (-1)` in real tangent-space dimension `n`. -/
theorem IsHyperbolic.exists_scalarCurvature_eq
    (h : IsHyperbolic (I := I) (M := M)) :
    ∃ g : HyperbolicMetric (I := I) (M := M),
      ∀ (x : M),
        letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨g.metric.toRiemannianMetric⟩
        (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x =
          (Module.finrank ℝ (TangentSpace I x) : ℝ) *
            (Module.finrank ℝ (TangentSpace I x) - 1) * (-1 : ℝ) := by
  rcases h with ⟨g⟩
  refine ⟨g, fun x => ?_⟩
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨g.metric.toRiemannianMetric⟩
  apply CovariantDerivative.scalarCurvature_eq_of_curvatureTensor_eq_smul_inner_sub
  intro w u v
  exact g.curvatureTensor_eq x w u v

/-- An `IsHyperbolic` witness has constant sectional curvature `-1`. -/
theorem IsHyperbolic.exists_hasConstantSectionalCurvature
    (h : IsHyperbolic (I := I) (M := M)) :
    ∃ g : HyperbolicMetric (I := I) (M := M),
      letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨g.metric.toRiemannianMetric⟩
      (CovariantDerivative.leviCivitaConnection I M).HasConstantSectionalCurvature
        (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) (-1) := by
  rcases h with ⟨g⟩
  exact ⟨g, g.hasConstantSectionalCurvature⟩

end TauCeti
