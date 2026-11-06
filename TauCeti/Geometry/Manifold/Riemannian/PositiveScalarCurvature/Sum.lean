/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.PositiveScalarCurvature.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Sum.Topology
public import Mathlib.Topology.Connected.PathConnected

/-!
# Disjoint unions of isotopies of positive scalar curvature metrics

Isotopies of metrics of positive scalar curvature on two manifolds with the same model space
assemble into an isotopy on their disjoint union. The paths are continuous in the chart C²
topology on the native smooth metric carrier. Neither manifold needs to be compact: positivity
on a disjoint union is positivity on each summand, and the disjoint-union operation is jointly
continuous.

This is the family counterpart of
`Bundle.ContMDiffRiemannianMetric.HasPositiveScalarCurvature.sumTangentSpace`.
-/

public section

open Bundle Set
open scoped ContDiff Manifold TauCeti.MetricC2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  {N : Type*} [TopologicalSpace N] [T2Space N] [ChartedSpace H N] [IsManifold I ∞ N]
  {g₀ g₁ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
  {h₀ h₁ : ContMDiffRiemannianMetric I ∞ E (fun x : N ↦ TangentSpace I x)}

/-- Isotopies through metrics of positive scalar curvature assemble on disjoint unions, with
the given disjoint-union metrics as their exact endpoints. -/
theorem JoinedIn.sumTangentSpace
    (hg : JoinedIn {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) |
      g.HasPositiveScalarCurvature} g₀ g₁)
    (hh : JoinedIn {h : ContMDiffRiemannianMetric I ∞ E (fun x : N ↦ TangentSpace I x) |
      h.HasPositiveScalarCurvature} h₀ h₁) :
    JoinedIn {G : ContMDiffRiemannianMetric I ∞ E (fun x : M ⊕ N ↦ TangentSpace I x) |
      G.HasPositiveScalarCurvature} (g₀.sumTangentSpace h₀) (g₁.sumTangentSpace h₁) := by
  have hcont := ContMDiffRiemannianMetric.continuous_sumTangentSpace (I := I)
    (M := M) (N := N) 2 continuous_fst continuous_snd
  refine ((hg.prod hh).map hcont.continuousOn).mono ?_
  rintro _ ⟨⟨g, h⟩, ⟨hg, hh⟩, rfl⟩
  exact hg.sumTangentSpace hh
