/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.PositiveScalarCurvature.Family

/-!
# Stability of positive scalar curvature in metric families

A family of smooth metrics with jointly continuous chart derivatives through order two has
jointly continuous scalar curvature. If its scalar curvature is positive on a compact product
of parameters and spatial points, a common positive lower bound persists on a neighbourhood
of the whole parameter set, uniformly over the spatial set. Neither the parameter space nor
the manifold needs to be compact. In particular, on a compact manifold, the parameters giving
metrics of positive scalar curvature form an open set.

The neighbourhood bound permits perturbations of compact parameter families while retaining a
positive scalar margin, as needed when smoothing paths of metrics. The hypotheses concern actual
coordinate derivatives of native metrics; no topology on the space of metrics is installed here.
The second-order continuity and compact-set scalar bound are supplied by
`TauCeti.Manifold.continuousAt_scalarCurvature_of_continuousAt_chartMetric` and
`TauCeti.Manifold.exists_pos_le_scalarCurvature_of_isCompact`.

## References

* M. Gromov, H. B. Lawson, *The classification of simply connected manifolds of positive
  scalar curvature*, Ann. of Math. 111 (1980), 423–434.
-/

public section

open Bundle Module Set Filter
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  {P : Type*} [TopologicalSpace P]
  (g : P → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
  {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ E)

/-- A compact family with positive scalar curvature on a compact spatial set retains a uniform
positive scalar bound on a neighbourhood of its parameter set. Joint continuity of the chart
metric and its first two derivatives is required only at the tested parameters and points. -/
theorem exists_pos_eventually_forall_le_scalarCurvature
    {K : Set P} (hK : IsCompact K) {L : Set M} (hL : IsCompact L)
    (h₀ : ∀ p ∈ K, ∀ x ∈ L, ContinuousAt (fun r : P × E ↦ LinearMap.toMatrix₂ b b
      ((g r.1).toNondegenerateMetric.chartMetric x r.2).toBilinForm) (p, extChartAt I x x))
    (h₁ : ∀ p ∈ K, ∀ x ∈ L, ContinuousAt (fun r : P × E ↦ fun k i j ↦
      fderiv ℝ (fun z ↦ (g r.1).toNondegenerateMetric.chartMetric x z (b i) (b j)) r.2 (b k))
      (p, extChartAt I x x))
    (h₂ : ∀ p ∈ K, ∀ x ∈ L, ContinuousAt (fun r : P × E ↦ fun m k i j ↦ fderiv ℝ
      (fun z ↦ fderiv ℝ (fun z' ↦ (g r.1).toNondegenerateMetric.chartMetric x z' (b i) (b j))
        z (b k)) r.2 (b m)) (p, extChartAt I x x))
    (hpos : ∀ p ∈ K, ∀ x ∈ L, 0 < (g p).scalarCurvature x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ p in 𝓝ˢ K, ∀ x ∈ L, ε ≤ (g p).scalarCurvature x := by
  have hcont (p : P) (hp : p ∈ K) (x : M) (hx : x ∈ L) :
      ContinuousAt (fun q : P × M ↦ (g q.1).scalarCurvature q.2) (p, x) :=
    continuousAt_scalarCurvature_of_continuousAt_chartMetric b g
      (by simp [ModelWithCorners.Boundaryless.range_eq_univ])
      (h₀ p hp x hx) (h₁ p hp x hx) (h₂ p hp x hx)
  obtain ⟨δ, hδ, hbound⟩ := exists_pos_le_scalarCurvature_of_isCompact g b (hK.prod hL)
    (fun q hq ↦ h₀ q.1 hq.1 q.2 hq.2) (fun q hq ↦ h₁ q.1 hq.1 q.2 hq.2)
    (fun q hq ↦ h₂ q.1 hq.1 q.2 hq.2) (fun q hq ↦ hpos q.1 hq.1 q.2 hq.2)
  refine ⟨δ / 2, by positivity, mem_nhdsSet_iff_forall.mpr fun p hp ↦ ?_⟩
  have hnear : {q : P × M | δ / 2 < (g q.1).scalarCurvature q.2} ∈
      (𝓝 p) ×ˢ (𝓝ˢ L) :=
    hL.mem_prod_nhdsSet_of_forall fun x hx ↦ by
      rw [← nhds_prod_eq]
      exact (hcont p hp x hx).preimage_mem_nhds
        (Ioi_mem_nhds (lt_of_lt_of_le (by linarith) (hbound (p, x) ⟨hp, hx⟩)))
  filter_upwards [Filter.Eventually.curry hnear] with q hq
  exact fun x hx ↦ (hq.self_of_nhdsSet x hx).le

/-- On a compact manifold, the parameters of a family with jointly continuous chart derivatives
through order two for which the metric has positive scalar curvature form an open set. -/
theorem isOpen_setOf_hasPositiveScalarCurvature [CompactSpace M]
    (h₀ : ∀ p x, ContinuousAt (fun r : P × E ↦ LinearMap.toMatrix₂ b b
      ((g r.1).toNondegenerateMetric.chartMetric x r.2).toBilinForm) (p, extChartAt I x x))
    (h₁ : ∀ p x, ContinuousAt (fun r : P × E ↦ fun k i j ↦
      fderiv ℝ (fun z ↦ (g r.1).toNondegenerateMetric.chartMetric x z (b i) (b j)) r.2 (b k))
      (p, extChartAt I x x))
    (h₂ : ∀ p x, ContinuousAt (fun r : P × E ↦ fun m k i j ↦ fderiv ℝ (fun z ↦ fderiv ℝ
      (fun z' ↦ (g r.1).toNondegenerateMetric.chartMetric x z' (b i) (b j)) z (b k)) r.2 (b m))
      (p, extChartAt I x x)) :
    IsOpen {p | (g p).HasPositiveScalarCurvature} := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  obtain ⟨ε, hε, hnear⟩ := exists_pos_eventually_forall_le_scalarCurvature g b
    (K := {p}) isCompact_singleton (L := univ) isCompact_univ
    (fun q _ x _ ↦ h₀ q x) (fun q _ x _ ↦ h₁ q x) (fun q _ x _ ↦ h₂ q x)
    (fun q hq x _ ↦ by
      simpa only [mem_singleton_iff.mp hq] using (g p).hasPositiveScalarCurvature_iff.mp hp x)
  rw [nhdsSet_singleton] at hnear
  filter_upwards [hnear] with q hq
  exact (g q).hasPositiveScalarCurvature_iff.mpr fun x ↦ hε.trans_le (hq x (mem_univ x))

end TauCeti.Manifold
