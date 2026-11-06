/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Topology.MetricSpace.Antilipschitz
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Tangent cones containing differentiable images

At a differentiability point of a parametrization with a Lipschitz inverse, the image lies
locally in every cone around the range of the derivative. The inverse bound is essential:
it prevents distant parameters from returning arbitrarily close to the image point.

This pointwise estimate is the geometric input for approximate tangent planes of rectifiable
sets. It does not require measurability, finite dimension, or injectivity of the derivative.
-/

public section

open Set Filter Metric
open scoped Topology NNReal

/-- Near the image of a differentiability point, an inverse-Lipschitz parametrization lies
in every cone about the range of its derivative. The estimate includes the cone vertex. -/
theorem HasFDerivWithinAt.exists_pos_forall_infDist_range_le
    {𝕜 U V : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup U] [NormedSpace 𝕜 U]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] {f : U → V} {s : Set U} {x : U}
    {A : U →L[𝕜] V} (hd : HasFDerivWithinAt f A s x) (hx : x ∈ s)
    {K : ℝ≥0} (hi : AntilipschitzWith K (s.domRestrict f)) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∀ y ∈ f '' s, dist y (f x) < r →
      infDist (y - f x) (LinearMap.range A.toLinearMap : Set V) ≤ ε * dist y (f x) := by
  let C : ℝ := K + 1
  have hC : 0 < C := by positivity
  have hbound := hd.isLittleO.bound (div_pos hε hC)
  obtain ⟨δ, hδ, hδbound⟩ := eventually_nhds_iff_ball.mp
    (eventually_nhdsWithin_iff.mp hbound)
  refine ⟨δ / C, div_pos hδ hC, ?_⟩
  rintro _ ⟨z, hz, rfl⟩ hdist
  have hinv : dist z x ≤ C * dist (f z) (f x) := by
    exact (hi.le_mul_dist ⟨z, hz⟩ ⟨x, hx⟩).trans
      (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) dist_nonneg)
  have hzδ : z ∈ ball x δ := by
    rw [mem_ball]
    exact hinv.trans_lt (by simpa only [mul_comm] using (lt_div_iff₀ hC).mp hdist)
  calc
    infDist (f z - f x) (LinearMap.range A.toLinearMap : Set V) ≤ dist (f z - f x) (A (z - x)) :=
      infDist_le_dist_of_mem ⟨z - x, rfl⟩
    _ ≤ (ε / C) * ‖z - x‖ := by
      simpa only [dist_eq_norm] using hδbound z hzδ hz
    _ ≤ (ε / C) * (C * dist (f z) (f x)) := by
      gcongr
      simpa only [dist_eq_norm] using hinv
    _ = ε * dist (f z) (f x) := by field_simp
