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

The bound also holds relative to a closed set `C` near which the family is fixed: if every `g p`
agrees with one metric `g₀` on a common neighbourhood of `C`, then the scalar curvature of `g p`
is that of `g₀` there, so positivity of the scalar curvature of `g₀` on `C` together with the
hypotheses above at the points outside `C` already gives a uniform positive lower bound. No
continuity in the parameter needs to be checked near `C`.

This uniform scalar gap is the margin consumed when a compact family of metrics of positive scalar
curvature is perturbed, for instance when a path of such metrics is smoothed or reparametrized.

## Main results

* `TauCeti.Manifold.exists_pos_le_scalarCurvature_of_isCompact`: a uniform positive lower bound
  on a compact set of parameters and points where the scalar curvature is positive.
* `TauCeti.Manifold.exists_pos_forall_le_scalarCurvature`: a compact family of metrics of positive
  scalar curvature on a compact manifold has a common positive lower bound.
* `TauCeti.Manifold.exists_pos_le_scalarCurvature_of_isCompact_of_eventually_inner_eq`: a uniform
  positive lower bound on a compact set of parameters and points for a family fixed near a closed
  set.
* `TauCeti.Manifold.exists_pos_forall_le_scalarCurvature_of_eventually_inner_eq`: on a compact
  manifold, a compact family fixed near a closed set and of positive scalar curvature away from it
  has a common positive lower bound.

## References

* M. Gromov, H. B. Lawson, *The classification of simply connected manifolds of positive
  scalar curvature*, Ann. of Math. 111 (1980), 423–434.
-/

public section

open Bundle Module Set TauCeti.Manifold
open scoped ContDiff Manifold Topology

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

/-- **A uniform scalar-curvature gap relative to a closed set.** Let `g p` be a family of metrics,
all of which agree with a fixed metric `g₀` on a common neighbourhood of a closed set `C`, and let
`S ⊆ P × M` be compact. Suppose that the scalar curvature of `g₀` is positive at `x` for every
`(p, x) ∈ S` with `x ∈ C`, and that for every `(p, x) ∈ S` with `x ∉ C` the scalar curvature of
`g p` is positive at `x` and the chart metrics have Gram matrices, first and second derivatives in
the basis `b` depending continuously on the parameter and the chart point. Then the scalar
curvature is bounded below on `S` by a positive constant. -/
theorem exists_pos_le_scalarCurvature_of_isCompact_of_eventually_inner_eq {S : Set (P × M)}
    (hS : IsCompact S) {C : Set M} (hC : IsClosed C)
    (g₀ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hfix : ∀ᶠ x in 𝓝ˢ C, ∀ p, (g p).inner x = g₀.inner x)
    (h₀ : ∀ q ∈ S, q.2 ∉ C → ContinuousAt (fun r : P × E ↦ LinearMap.toMatrix₂ b b
      ((g r.1).toNondegenerateMetric.chartMetric q.2 r.2).toBilinForm)
      (q.1, extChartAt I q.2 q.2))
    (h₁ : ∀ q ∈ S, q.2 ∉ C → ContinuousAt (fun r : P × E ↦ fun k i j ↦
      fderiv ℝ (fun z ↦ (g r.1).toNondegenerateMetric.chartMetric q.2 z (b i) (b j)) r.2 (b k))
      (q.1, extChartAt I q.2 q.2))
    (h₂ : ∀ q ∈ S, q.2 ∉ C → ContinuousAt (fun r : P × E ↦ fun m k i j ↦ fderiv ℝ (fun z ↦
      fderiv ℝ (fun z' ↦ (g r.1).toNondegenerateMetric.chartMetric q.2 z' (b i) (b j)) z (b k))
      r.2 (b m)) (q.1, extChartAt I q.2 q.2))
    (hpos₀ : ∀ q ∈ S, q.2 ∈ C → 0 < g₀.scalarCurvature q.2)
    (hpos : ∀ q ∈ S, q.2 ∉ C → 0 < (g q.1).scalarCurvature q.2) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q ∈ S, ε ≤ (g q.1).scalarCurvature q.2 := by
  obtain ⟨U, hUo, hCU, hU⟩ := mem_nhdsSet_iff_exists.1 hfix
  -- On `U` every `g p` has the scalar curvature of `g₀`, which is at least `δ` at the points of
  -- `C` lying under `S`.
  have hscal (p : P) : EqOn (g p).scalarCurvature g₀.scalarCurvature U :=
    ContMDiffRiemannianMetric.eqOn_scalarCurvature hUo fun x hx ↦ hU hx p
  obtain ⟨δ, hδ, hδle⟩ := ((hS.image continuous_snd).inter_right hC).exists_forall_le'
    g₀.continuous_scalarCurvature.continuousOn fun _ ⟨⟨q, hq, hqx⟩, hxC⟩ ↦
      hqx ▸ hpos₀ q hq (hqx ▸ hxC)
  -- The open set `W` contains these points of `C`, and on the compact part of `S` lying over the
  -- complement of `W` the family satisfies the hypotheses of the absolute bound.
  let W := U ∩ {x | δ / 2 < g₀.scalarCurvature x}
  have hW : IsOpen W := hUo.inter (isOpen_lt continuous_const g₀.continuous_scalarCurvature)
  have hSW : ∀ q ∈ S \ Prod.snd ⁻¹' W, q ∈ S ∧ q.2 ∉ C := fun q hq ↦
    ⟨hq.1, fun hqC ↦ hq.2 ⟨hCU hqC, half_lt_self hδ |>.trans_le
      (hδle q.2 ⟨⟨q, hq.1, rfl⟩, hqC⟩)⟩⟩
  obtain ⟨ε, hε, hle⟩ := exists_pos_le_scalarCurvature_of_isCompact g b
    (hS.diff (hW.preimage continuous_snd)) (fun q hq ↦ h₀ q (hSW q hq).1 (hSW q hq).2)
    (fun q hq ↦ h₁ q (hSW q hq).1 (hSW q hq).2) (fun q hq ↦ h₂ q (hSW q hq).1 (hSW q hq).2)
    fun q hq ↦ hpos q (hSW q hq).1 (hSW q hq).2
  refine ⟨min ε (δ / 2), by positivity, fun q hq ↦ ?_⟩
  by_cases hqW : q.2 ∈ W
  · rw [hscal q.1 hqW.1]
    exact (min_le_right _ _).trans hqW.2.le
  · exact (min_le_left _ _).trans (hle q ⟨hq, hqW⟩)

/-- **Compact families fixed near a closed set have a uniform scalar gap.** On a compact manifold,
let `g p` be a family of metrics, indexed by a compact space, all of which agree with a fixed
metric `g₀` on a common neighbourhood of a closed set `C`. If the scalar curvature of `g₀` is
positive on `C`, and outside `C` the scalar curvature of each `g p` is positive and the chart
metrics have Gram matrices, first and second derivatives in the basis `b` depending continuously
on the parameter and the chart point, then the scalar curvatures of the metrics `g p` are bounded
below by a common positive constant. -/
theorem exists_pos_forall_le_scalarCurvature_of_eventually_inner_eq [CompactSpace P]
    [CompactSpace M] {C : Set M} (hC : IsClosed C)
    (g₀ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hfix : ∀ᶠ x in 𝓝ˢ C, ∀ p, (g p).inner x = g₀.inner x)
    (h₀ : ∀ p, ∀ x ∉ C, ContinuousAt (fun r : P × E ↦ LinearMap.toMatrix₂ b b
      ((g r.1).toNondegenerateMetric.chartMetric x r.2).toBilinForm) (p, extChartAt I x x))
    (h₁ : ∀ p, ∀ x ∉ C, ContinuousAt (fun r : P × E ↦ fun k i j ↦
      fderiv ℝ (fun z ↦ (g r.1).toNondegenerateMetric.chartMetric x z (b i) (b j)) r.2 (b k))
      (p, extChartAt I x x))
    (h₂ : ∀ p, ∀ x ∉ C, ContinuousAt (fun r : P × E ↦ fun m k i j ↦ fderiv ℝ (fun z ↦ fderiv ℝ
      (fun z' ↦ (g r.1).toNondegenerateMetric.chartMetric x z' (b i) (b j)) z (b k)) r.2 (b m))
      (p, extChartAt I x x))
    (hpos₀ : ∀ x ∈ C, 0 < g₀.scalarCurvature x)
    (hpos : ∀ p, ∀ x ∉ C, 0 < (g p).scalarCurvature x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ p x, ε ≤ (g p).scalarCurvature x := by
  obtain ⟨ε, hε, hle⟩ := exists_pos_le_scalarCurvature_of_isCompact_of_eventually_inner_eq g b
    isCompact_univ hC g₀ hfix (fun q _ ↦ h₀ q.1 q.2) (fun q _ ↦ h₁ q.1 q.2)
    (fun q _ ↦ h₂ q.1 q.2) (fun q _ ↦ hpos₀ q.2) fun q _ ↦ hpos q.1 q.2
  exact ⟨ε, hε, fun p x ↦ hle (p, x) (mem_univ _)⟩

end TauCeti.Manifold
