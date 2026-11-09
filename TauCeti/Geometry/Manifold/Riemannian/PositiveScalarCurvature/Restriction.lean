/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.PositiveScalarCurvature.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Restriction.Topology
public import Mathlib.Topology.Connected.PathConnected

/-!
# Restriction of positive-scalar-curvature isotopies

A path of metrics of positive scalar curvature restricts to such a path on every open
submanifold, with the restrictions of the original endpoint metrics as its endpoints.
The topology on metrics is the chart C² topology, as in the isotopy-to-concordance theorem.
Neither the ambient manifold nor the open submanifold needs to be compact.
-/

public section

open Bundle Set
open scoped ContDiff Manifold TauCeti.MetricC2

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A C²-continuous isotopy of metrics of positive scalar curvature restricts to an isotopy on
any open submanifold, preserving the endpoint metrics by restriction. -/
theorem JoinedIn.restrictOpenTangentSpace
    {g₀ g₁ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    (h : JoinedIn {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) |
      g.HasPositiveScalarCurvature} g₀ g₁) (U : TopologicalSpace.Opens M) :
    JoinedIn {g : ContMDiffRiemannianMetric I ∞ E (fun x : U ↦ TangentSpace I x) |
      g.HasPositiveScalarCurvature}
      (g₀.restrictOpenTangentSpace U) (g₁.restrictOpenTangentSpace U) := by
  refine (h.map (ContMDiffRiemannianMetric.continuous_restrictOpenTangentSpace 2 U).continuousOn)
    |>.mono ?_
  rintro _ ⟨g, hg, rfl⟩
  exact hg.restrictOpenTangentSpace U
