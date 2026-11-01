/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Distance
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

On a compact manifold completeness is automatic, so there a hyperbolic metric is just a smooth
metric of constant curvature `-1` (`TauCeti.HyperbolicMetric.ofCompactSpace`,
`TauCeti.isHyperbolic_iff_exists_isConstantCurvatureTensor`).
-/

public section

open Bundle
open scoped ContDiff Manifold

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

namespace TauCeti

/-- A complete smooth Riemannian metric of constant curvature `-1` on `M`. -/
@[ext]
structure HyperbolicMetric where
  /-- The smooth Riemannian metric. -/
  metric : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)
  /-- The metric's own Riemannian distance is metrically complete. -/
  complete : letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨metric.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
      IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
        (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)
    @CompleteSpace M
      (MetricSpace.ofRiemannianMetric I M).toPseudoMetricSpace.toUniformSpace
  /-- The Levi-Civita connection has the constant-curvature tensor with parameter `-1`. -/
  curvature : Bundle.ContMDiffRiemannianMetric.IsConstantCurvatureTensor
    (I := I) (M := M) metric (-1)

/-- A manifold is hyperbolic when it admits a complete smooth metric of constant curvature `-1`.

This is the existence predicate used by later hyperbolic-volume and Mostow-rigidity statements;
the chosen metric remains available through `HyperbolicMetric` when a proof is needed. -/
def IsHyperbolic : Prop := Nonempty (HyperbolicMetric (I := I) (M := M))

/-- A manifold is hyperbolic exactly when it carries a hyperbolic metric. -/
theorem isHyperbolic_iff : IsHyperbolic (I := I) (M := M) ↔
    Nonempty (HyperbolicMetric (I := I) (M := M)) :=
  Iff.rfl

namespace HyperbolicMetric

/-- On a compact manifold every smooth metric of constant curvature `-1` is a hyperbolic metric:
a compact metric space is complete, so completeness of the Riemannian distance is automatic. -/
def ofCompactSpace [CompactSpace M]
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    (hg : g.IsConstantCurvatureTensor (-1)) : HyperbolicMetric (I := I) (M := M) where
  metric := g
  complete :=
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
      IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
        (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)
    letI : MetricSpace M := MetricSpace.ofRiemannianMetric I M
    complete_of_compact
  curvature := hg

@[simp]
theorem metric_ofCompactSpace [CompactSpace M]
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    (hg : g.IsConstantCurvatureTensor (-1)) : (ofCompactSpace hg).metric = g :=
  (rfl)

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

/-- A compact manifold is hyperbolic exactly when it carries a smooth metric of constant curvature
`-1`; completeness is automatic. -/
theorem isHyperbolic_iff_exists_isConstantCurvatureTensor [CompactSpace M] :
    IsHyperbolic (I := I) (M := M) ↔
      ∃ g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x),
        g.IsConstantCurvatureTensor (-1) :=
  ⟨fun ⟨G⟩ ↦ ⟨G.metric, G.curvature⟩, fun ⟨_, hg⟩ ↦ ⟨HyperbolicMetric.ofCompactSpace hg⟩⟩

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
