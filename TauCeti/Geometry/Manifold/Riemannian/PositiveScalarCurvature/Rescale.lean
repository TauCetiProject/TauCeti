/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.PositiveScalarCurvature.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Rescale
public import Mathlib.Topology.Connected.PathConnected
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Rescaling isotopies of metrics of positive scalar curvature

A metric of positive scalar curvature and any positive constant rescaling are joined by a path
of metrics of positive scalar curvature, continuous in every chart Cᵏ topology. The path is
`t ↦ exp(t log c) g`. It does not require the manifold to be compact: each scale is positive,
so the constant-rescaling scalar-curvature law preserves positivity at every point.

The continuity is the metric-family rescaling law
`Bundle.ContMDiffRiemannianMetric.continuous_rescale_const_chartCk`; positivity uses
`Bundle.ContMDiffRiemannianMetric.HasPositiveScalarCurvature.rescale_const`.
-/

public section

noncomputable section

open Bundle Set
open scoped ContDiff Manifold

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}

/-- Positive constant rescaling preserves the isotopy class of a metric of positive scalar
curvature, in every chart Cᵏ topology. Compactness of the manifold is unnecessary. -/
theorem HasPositiveScalarCurvature.joinedIn_rescale_const (h : g.HasPositiveScalarCurvature)
    (k : ℕ∞) {c : ℝ} (hc : 0 < c) :
    letI := chartCkTopology (I := I) (M := M) k
    JoinedIn {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) |
      g.HasPositiveScalarCurvature} g
      (g.rescale (fun _ ↦ c) contMDiff_const (fun _ ↦ hc)) := by
  let _ := chartCkTopology (I := I) (M := M) k
  refine ⟨{
    toFun := fun t ↦ g.rescale (fun _ ↦ Real.exp ((t : ℝ) * Real.log c)) contMDiff_const
      (fun _ ↦ Real.exp_pos _)
    continuous_toFun := continuous_rescale_const_chartCk k (fun _ ↦ Real.exp_pos _)
      continuous_const (Real.continuous_exp.comp (continuous_subtype_val.mul_const _))
    source' := by simp
    target' := by simp [Real.exp_log hc] }, fun t ↦ ?_⟩
  exact h.rescale_const (Real.exp_pos _)

end Bundle.ContMDiffRiemannianMetric
