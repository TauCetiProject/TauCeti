/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Distance

/-!
# Compact closed metric balls in a normal domain

If a closed tangent ball lies in a normal domain at `p`, the closed metric ball of the same
radius about `p` is its exponential image, hence compact. No completeness is assumed.
-/

public section

open Bundle Function Manifold Set
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M] {p : M}

/-- A closed metric ball whose tangent ball lies in a normal domain is compact. -/
theorem IsNormalDomain.isCompact_closedBall {V : Set (TangentSpace I p)}
    (h : IsNormalDomain I M p V) {r : ℝ} (hball : Metric.closedBall 0 r ⊆ V) :
    IsCompact (Metric.closedBall p r) := by
  by_cases hr : 0 ≤ r
  · have himage : riemannianExp I M p '' Metric.closedBall 0 r = Metric.closedBall p r := by
      simpa only [Metric.closedEBall_ofReal hr] using h.image_riemannianExp_closedBall hball hr
    rw [← himage]
    exact (ProperSpace.isCompact_closedBall (0 : TangentSpace I p) r).image_of_continuousOn
      ((contMDiffOn_riemannianExp p).continuousOn.mono (hball.trans h.subset_expDomain))
  · have hempty : Metric.closedBall p r = ∅ := by
      ext x
      simp only [Metric.mem_closedBall, Set.mem_empty_iff_false, iff_false]
      intro hx
      exact hr (dist_nonneg.trans hx)
    simp [hempty]

end TauCeti.Manifold
