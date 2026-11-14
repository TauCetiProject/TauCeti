/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.MetricSpace.GeodesicPath
import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.Topology.ContinuousMap.Ascoli
import TauCeti.Topology.MetricSpace.Length.Lipschitz

/-!
# Proper length spaces are geodesic

In a length space, let the closed ball of radius `R` about `x` be compact and let
`dist x y < R`. For `r` slightly larger than `dist x y`, the points `x` and `y` are joined by an
`r`-Lipschitz path on the unit interval (`TauCeti.IsLengthSpace.exists_lipschitz_path`). These
paths stay in the compact ball, so by the Arzelà–Ascoli theorem a subsequence converges uniformly
as `r` decreases to `dist x y`. The limit is a `dist x y`-Lipschitz path from `x` to `y`, hence a
geodesic segment. In particular, a proper length space is a geodesic space. No completeness
beyond the compactness of one closed ball is needed.

## Main results

* `TauCeti.exists_isGeodesicSegment_of_isCompact_closedBall`: in a length space, a point of the
  open ball of radius `R` about `x` is joined to `x` by a geodesic segment when the closed ball of
  radius `R` about `x` is compact.
* `TauCeti.isGeodesicSpace_of_properSpace`: a proper length space is a geodesic space.

## References

* D. Burago, Y. Burago, and S. Ivanov, *A Course in Metric Geometry*, AMS, 2001, Section 2.5.
-/

public section

open Filter Set
open scoped NNReal Topology unitInterval

namespace TauCeti

variable {X : Type*} [MetricSpace X] [IsLengthSpace X]

/-- In a length space, if the closed ball of radius `R` about `x` is compact, then every point at
distance less than `R` from `x` is joined to `x` by a geodesic segment. -/
theorem exists_isGeodesicSegment_of_isCompact_closedBall {x y : X} {R : ℝ}
    (hR : IsCompact (Metric.closedBall x R)) (hxy : dist x y < R) :
    ∃ γ : ℝ → X, IsGeodesicSegment γ x y := by
  set r : ℕ → ℝ := fun n ↦ dist x y + (R - dist x y) / (n + 1)
  have hr (n : ℕ) : dist x y < r n := lt_add_of_pos_right _ (by have := sub_pos.2 hxy; positivity)
  have hrR (n : ℕ) : r n ≤ R := by
    have : (R - dist x y) / (n + 1) ≤ R - dist x y :=
      div_le_self (sub_nonneg.2 hxy.le) (by linarith [n.cast_nonneg (α := ℝ)])
    linarith
  choose f hf0 hf1 hfLip using fun n ↦ IsLengthSpace.exists_lipschitz_path (hr n)
  have hR0 : 0 ≤ R := dist_nonneg.trans hxy.le
  have hfmem (n : ℕ) : f n ∈ {g : C(I, X) | LipschitzWith R.toNNReal g ∧ g 0 = x} :=
    ⟨(hfLip n).weaken (Real.toNNReal_le_toNNReal (hrR n)), hf0 n⟩
  obtain ⟨g, ⟨-, hg0⟩, φ, hφ, hlim⟩ :=
    (isCompact_setOf_lipschitzWith_apply_zero_eq_of_isCompact_closedBall R.toNNReal x
      (by rwa [Real.coe_toNNReal _ hR0])).tendsto_subseq hfmem
  have hpoint (t : I) : Tendsto (fun n ↦ f (φ n) t) atTop (𝓝 (g t)) :=
    ((continuous_eval_const t).tendsto g).comp hlim
  have hg1 : g 1 = y :=
    tendsto_nhds_unique (hpoint 1) (by simpa only [hf1] using tendsto_const_nhds)
  have hrlim : Tendsto r atTop (𝓝 (dist x y)) := by
    simpa only [mul_zero, add_zero, mul_one_div] using tendsto_const_nhds.add
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (R - dist x y))
  have hgLip : LipschitzWith (dist (g 0) (g 1)).toNNReal g := by
    rw [hg0, hg1]
    refine LipschitzWith.of_dist_le_mul fun s t ↦ ?_
    rw [Real.coe_toNNReal _ dist_nonneg]
    refine le_of_tendsto_of_tendsto' ((hpoint s).dist (hpoint t))
      ((hrlim.comp hφ.tendsto_atTop).mul_const (dist s t)) fun n ↦ ?_
    simpa only [Function.comp_apply, Real.coe_toNNReal _ (dist_nonneg.trans_lt (hr (φ n))).le]
      using (hfLip (φ n)).dist_le_mul s t
  rw [← exists_mem_geodesicPaths_iff]
  exact ⟨g, mem_geodesicPaths_of_lipschitzWith hgLip, hg0, hg1⟩

/-- **A proper length space is a geodesic space.** -/
theorem isGeodesicSpace_of_properSpace [ProperSpace X] : IsGeodesicSpace X :=
  ⟨fun x y ↦ exists_isGeodesicSegment_of_isCompact_closedBall
    (isCompact_closedBall x (dist x y + 1)) (lt_add_one _)⟩

end TauCeti
