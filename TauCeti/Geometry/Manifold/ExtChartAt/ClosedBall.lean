/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.ExtChartAt
import Mathlib.Tactic

/-!
# Closed coordinate balls

A closed ball contained in an extended chart target pulls back to a compact subset of the chart
source. Its membership is the closed coordinate-distance inequality, and the corresponding
strict inequality places a point in its interior. No smoothness or Riemannian metric is needed.

## Main results

* `TauCeti.Manifold.chart_closedBall_properties`: compactness, membership and interior criteria.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Corollary 4.14.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public noncomputable section
open Set Topology Metric
open scoped Manifold

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-- A closed ball contained in a manifold chart pulls back to a compact subset
of the chart source, with the expected membership and interior-ball criteria. -/
theorem chart_closedBall_properties
    (p : M) (c : E) {R : ℝ}
    (hball : closedBall c R ⊆ (extChartAt 𝓘(ℝ, E) p).target) :
    let e := extChartAt 𝓘(ℝ, E) p
    let C := e.symm '' closedBall c R
    IsCompact C ∧ C ⊆ e.source ∧
      (∀ x ∈ e.source, x ∈ C ↔ ‖e x - c‖ ≤ R) ∧
      (∀ x ∈ e.source, ‖e x - c‖ < R → x ∈ interior C) := by
  let e := extChartAt 𝓘(ℝ, E) p
  let C := e.symm '' closedBall c R
  have hC : IsCompact C := (isCompact_closedBall c R).image_of_continuousOn
    ((continuousOn_extChartAt_symm p).mono hball)
  have hCs : C ⊆ e.source := by
    rintro x ⟨z, hz, rfl⟩
    exact e.map_target (hball hz)
  have hmem (x : M) (hx : x ∈ e.source) : x ∈ C ↔ ‖e x - c‖ ≤ R := by
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [e.right_inv (hball hz)]
      exact mem_closedBall_iff_norm.mp hz
    · intro hnorm
      exact ⟨e x, mem_closedBall_iff_norm.mpr hnorm, e.left_inv hx⟩
  refine ⟨hC, hCs, hmem, ?_⟩
  intro x hx hnorm
  have hO : IsOpen (e.source ∩ e ⁻¹' ball c R) :=
    (continuousOn_extChartAt p).isOpen_inter_preimage (isOpen_extChartAt_source p) isOpen_ball
  have hOC : e.source ∩ e ⁻¹' ball c R ⊆ C := by
    intro y hy
    exact (hmem y hy.1).2 (mem_ball_iff_norm.mp hy.2).le
  exact mem_interior.mpr ⟨e.source ∩ e ⁻¹' ball c R, hOC, hO,
    hx, mem_ball_iff_norm.mpr hnorm⟩


end TauCeti.Manifold
