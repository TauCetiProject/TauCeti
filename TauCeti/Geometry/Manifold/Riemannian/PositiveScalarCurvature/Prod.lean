/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.PositiveScalarCurvature.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Prod
public import Mathlib.Topology.Connected.PathConnected

/-!
# Products of isotopies of positive scalar curvature metrics

An isotopy of metrics of positive scalar curvature on `M` and a path of metrics of nonnegative
scalar curvature on `N` multiply to an isotopy of metrics of positive scalar curvature on
`M × N`. The paths are continuous in the chart C² topology on the native smooth metric carrier.
Neither manifold needs to be compact: the scalar curvature of a product metric is the sum of the
scalar curvatures of the factors, and the product operation is jointly continuous
(`Bundle.ContMDiffRiemannianMetric.continuous_prodTangentSpace`).

This is the family counterpart of
`Bundle.ContMDiffRiemannianMetric.HasPositiveScalarCurvature.prodTangentSpace_of_nonneg`. Taking
the path on `N` constant, an isotopy `g₀ ≃ g₁` gives an isotopy `g₀ × h ≃ g₁ × h` for every metric
`h` of nonnegative scalar curvature, such as a flat or round factor.
-/

public section

open Bundle Set
open scoped ContDiff Manifold TauCeti.MetricC2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [T2Space N] [ChartedSpace G N] [IsManifold J ∞ N]
  {g₀ g₁ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
  {h₀ h₁ : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y)}

/-- The product of an isotopy through metrics of positive scalar curvature with a path through
metrics of nonnegative scalar curvature is an isotopy through metrics of positive scalar curvature,
with the given product metrics as its exact endpoints. -/
theorem JoinedIn.prodTangentSpace
    (hg : JoinedIn {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) |
      g.HasPositiveScalarCurvature} g₀ g₁)
    (hh : JoinedIn {h : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y) |
      ∀ y, 0 ≤ h.scalarCurvature y} h₀ h₁) :
    JoinedIn {G : ContMDiffRiemannianMetric (I.prod J) ∞ (E × F)
        (fun p : M × N ↦ TangentSpace (I.prod J) p) | G.HasPositiveScalarCurvature}
      (g₀.prodTangentSpace h₀) (g₁.prodTangentSpace h₁) := by
  have hcont := ContMDiffRiemannianMetric.continuous_prodTangentSpace (I := I) (J := J)
    (M := M) (N := N) 2 continuous_fst continuous_snd
  refine ((hg.prod hh).map hcont.continuousOn).mono ?_
  rintro _ ⟨⟨g, h⟩, ⟨hg, hh⟩, rfl⟩
  exact hg.prodTangentSpace_of_nonneg hh
