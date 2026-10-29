/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.PositiveScalarCurvature.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Jet

/-!
# Uniform positive scalar curvature for compact families of metrics

Let `g p` be a family of smooth Riemannian metrics on a manifold without boundary, indexed by a
topological space `P`. The family is continuous in the `C²` sense when, in the chart at each
point and in a fixed basis of the model, the Gram matrix of the chart metric and its first and
second derivatives depend jointly continuously on the parameter and the chart point. Scalar
curvature is a continuous function of this second-order jet wherever the Gram matrix is invertible
(`ContinuousAt.scalarCurvatureOfJet`), so for such a family `(p, x) ↦ Scal(g p)(x)` is jointly
continuous. Consequently, on a compact set of parameters and points at which the scalar curvature
is positive, it has a uniform positive lower bound. In particular, a family of metrics of positive
scalar curvature on a compact manifold, indexed by a compact space, has a common positive lower
bound for its scalar curvature.

This uniform scalar gap is the margin consumed when a compact family of metrics of positive scalar
curvature is perturbed, for instance when a path of such metrics is smoothed or reparametrized.

## Main results

* `TauCeti.Manifold.exists_pos_le_scalarCurvature_of_isCompact`: a uniform positive lower bound
  on a compact set of parameters and points where the scalar curvature is positive.
* `TauCeti.Manifold.exists_pos_forall_le_scalarCurvature`: a compact family of metrics of positive
  scalar curvature on a compact manifold has a common positive lower bound.

## References

* M. Gromov, H. B. Lawson, *The classification of simply connected manifolds of positive
  scalar curvature*, Ann. of Math. 111 (1980), 423–434.
-/

public section

open Bundle Module Set TauCeti.Manifold
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  {P : Type*} [TopologicalSpace P]
  (g : P → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
  {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ E)

/-- **A uniform scalar-curvature gap on compact sets.** Let `g p` be a family of metrics whose
chart metrics have Gram matrices, first and second derivatives in the basis `b` depending
continuously on the parameter and the chart point at every point of a compact set
`S ⊆ P × M`. If the scalar curvature of `g p` is positive at `x` for every `(p, x) ∈ S`, then it is
bounded below on `S` by a positive constant. -/
theorem exists_pos_le_scalarCurvature_of_isCompact {S : Set (P × M)} (hS : IsCompact S)
    (h₀ : ∀ q ∈ S, ContinuousAt (fun r : P × E ↦ LinearMap.toMatrix₂ b b
      ((g r.1).toNondegenerateMetric.chartMetric q.2 r.2).toBilinForm)
      (q.1, extChartAt I q.2 q.2))
    (h₁ : ∀ q ∈ S, ContinuousAt (fun r : P × E ↦ fun k i j ↦
      fderiv ℝ (fun z ↦ (g r.1).toNondegenerateMetric.chartMetric q.2 z (b i) (b j)) r.2 (b k))
      (q.1, extChartAt I q.2 q.2))
    (h₂ : ∀ q ∈ S, ContinuousAt (fun r : P × E ↦ fun m k i j ↦ fderiv ℝ (fun z ↦ fderiv ℝ
      (fun z' ↦ (g r.1).toNondegenerateMetric.chartMetric q.2 z' (b i) (b j)) z (b k)) r.2 (b m))
      (q.1, extChartAt I q.2 q.2))
    (hpos : ∀ q ∈ S, 0 < (g q.1).scalarCurvature q.2) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q ∈ S, ε ≤ (g q.1).scalarCurvature q.2 :=
  hS.exists_forall_le' (fun q hq ↦ (continuousAt_scalarCurvature_of_continuousAt_chartMetric b g
    (by simp [ModelWithCorners.Boundaryless.range_eq_univ]) (h₀ q hq) (h₁ q hq)
    (h₂ q hq)).continuousWithinAt) hpos

/-- **Compact families of metrics of positive scalar curvature have a uniform scalar gap.** On a
compact manifold, a family of metrics of positive scalar curvature indexed by a compact space, whose
chart metrics have Gram matrices, first and second derivatives in the basis `b` depending
continuously on the parameter and the chart point, has scalar curvature bounded below by a common
positive constant. -/
theorem exists_pos_forall_le_scalarCurvature [CompactSpace P] [CompactSpace M]
    (h₀ : ∀ p x, ContinuousAt (fun r : P × E ↦ LinearMap.toMatrix₂ b b
      ((g r.1).toNondegenerateMetric.chartMetric x r.2).toBilinForm) (p, extChartAt I x x))
    (h₁ : ∀ p x, ContinuousAt (fun r : P × E ↦ fun k i j ↦
      fderiv ℝ (fun z ↦ (g r.1).toNondegenerateMetric.chartMetric x z (b i) (b j)) r.2 (b k))
      (p, extChartAt I x x))
    (h₂ : ∀ p x, ContinuousAt (fun r : P × E ↦ fun m k i j ↦ fderiv ℝ (fun z ↦ fderiv ℝ
      (fun z' ↦ (g r.1).toNondegenerateMetric.chartMetric x z' (b i) (b j)) z (b k)) r.2 (b m))
      (p, extChartAt I x x))
    (hpos : ∀ p, (g p).HasPositiveScalarCurvature) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ p x, ε ≤ (g p).scalarCurvature x := by
  obtain ⟨ε, hε, hle⟩ := exists_pos_le_scalarCurvature_of_isCompact g b isCompact_univ
    (fun q _ ↦ h₀ q.1 q.2) (fun q _ ↦ h₁ q.1 q.2) (fun q _ ↦ h₂ q.1 q.2)
    fun q _ ↦ (g q.1).hasPositiveScalarCurvature_iff.1 (hpos q.1) q.2
  exact ⟨ε, hε, fun p x ↦ hle (p, x) (mem_univ _)⟩

end TauCeti.Manifold
