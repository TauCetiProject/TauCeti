/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giada Franz, The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.Order.Compact

/-!
# Point picking along a map into a metric space

Let `g ⁻¹' closedBall x r₀` be compact, with `A` nonnegative and the weighted quantity
`(r₀ - d(g(y), x)) A(y)` continuous there. Maximizing that quantity gives a point `p`
such that, with
`d = r₀ - d(g(p), x)`,

* the weighted quantity at `p` is at least its value at any given point `q`;
* `A ≤ 2 A(p)` on `g⁻¹(B_{d/2}(g(p)))`.

This is the point-picking step of the blow-up arguments for minimal surfaces, applied with `A`
the norm of the second fundamental form.

## Main results

* `exists_point_picking`
-/

public section

open Metric Set

namespace Metric

variable {X Y : Type*} [TopologicalSpace X] [PseudoMetricSpace Y]

/-- **Point picking.** If `g ⁻¹' closedBall x r₀` is compact and the weighted quantity is
continuous there, `A ≥ 0` there, and `(r₀ - d(g(q), x)) A(q) > 0` for some `q` in the preimage, then
there is `p` with
`g(p) ∈ B_{r₀}(x)`, `(r₀ - d(g(q), x)) A(q) ≤ (r₀ - d(g(p), x)) A(p)`, and `A ≤ 2 A(p)` on
`g⁻¹(B_{d/2}(g(p)))`, where `d = r₀ - d(g(p), x)`. -/
theorem exists_point_picking {g : X → Y} {A : X → ℝ} {x : Y} {r₀ : ℝ}
    (hK : IsCompact (g ⁻¹' closedBall x r₀))
    (hcont : ContinuousOn (fun y ↦ (r₀ - dist (g y) x) * A y)
      (g ⁻¹' closedBall x r₀))
    (hA0 : ∀ y, g y ∈ closedBall x r₀ → 0 ≤ A y) {q : X}
    (hq : g q ∈ closedBall x r₀) (hpos : 0 < (r₀ - dist (g q) x) * A q) :
    ∃ p, g p ∈ ball x r₀ ∧ (r₀ - dist (g q) x) * A q ≤ (r₀ - dist (g p) x) * A p ∧
      ∀ y, dist (g y) (g p) < (r₀ - dist (g p) x) / 2 → A y ≤ 2 * A p := by
  obtain ⟨p, hpK, hmax⟩ := hK.exists_isMaxOn ⟨q, hq⟩ hcont
  have hqp : (r₀ - dist (g q) x) * A q ≤ (r₀ - dist (g p) x) * A p := hmax hq
  have hFp : 0 < (r₀ - dist (g p) x) * A p := hpos.trans_le hqp
  have hd : 0 < r₀ - dist (g p) x := by
    by_contra h
    push Not at h
    exact absurd hFp (not_lt.2 (mul_nonpos_of_nonpos_of_nonneg h (hA0 p hpK)))
  refine ⟨p, mem_ball.2 (by linarith), hqp, fun y hy ↦ ?_⟩
  set d := r₀ - dist (g p) x
  have hyx : dist (g y) x ≤ r₀ - d / 2 := by
    have := dist_triangle (g y) (g p) x
    linarith
  have hyK : g y ∈ closedBall x r₀ := mem_closedBall.2 (by linarith)
  have hy' : (r₀ - dist (g y) x) * A y ≤ d * A p := hmax hyK
  have hd2 : d / 2 ≤ r₀ - dist (g y) x := by linarith
  have h1 : d / 2 * A y ≤ d * A p :=
    (mul_le_mul_of_nonneg_right hd2 (hA0 y hyK)).trans hy'
  nlinarith [hA0 y hyK, hA0 p hpK]

end Metric
