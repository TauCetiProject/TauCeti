/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Spheres and balls in pseudo-metric spaces

A sphere of positive radius `r < R` lies in the open ball of radius `R` about the same centre
(`Metric.sphere_abs_subset_ball`); the radius is written `|r|`, as in circle integrals.

For `R > 0` and a ratio `c > 1`, the annuli `R c ^ k ≤ dist y x < R c ^ (k + 1)`, `k ∈ ℤ`, cover
the points at positive distance from `x` (`Metric.iUnion_ball_diff_ball_mul_zpow`). With `c = 2`
this is the dyadic decomposition used to split singular integrals into shells.

Along `l ×ˢ 𝓝 x`, a radius sequence tending to zero plus the distance to `x` eventually
stays below any positive `r` (`Metric.eventually_add_dist_lt_of_tendsto_zero`), so the closed
balls of those radii about the points near `x` eventually lie in `ball x r`.

On the real line, the extended distance from `b` to `a ≤ b` is `b - a`
(`Real.edist_eq_ofReal_sub_of_le`).
-/

public section

open Metric

/-- A sphere of positive radius `r < R` lies in the open ball of radius `R` about the same
centre; the radius is written `|r|`, as in circle integrals. -/
theorem Metric.sphere_abs_subset_ball {X : Type*} [PseudoMetricSpace X] {x : X} {r R : ℝ}
    (hr : r ∈ Set.Ioo 0 R) : sphere x |r| ⊆ ball x R := by
  rw [abs_of_pos hr.1]
  exact sphere_subset_ball hr.2

/-- For `R > 0` and `c > 1`, the annuli `R c ^ k ≤ dist y x < R c ^ (k + 1)`, `k ∈ ℤ`, cover
exactly the points at positive distance from `x`, the complement of `closedBall x 0`. In a metric
space that complement is `{x}ᶜ` (`Metric.closedBall_zero`). -/
theorem Metric.iUnion_ball_diff_ball_mul_zpow {X : Type*} [PseudoMetricSpace X] (x : X)
    {R c : ℝ} (hR : 0 < R) (hc : 1 < c) :
    ⋃ k : ℤ, ball x (R * c ^ (k + 1)) \ ball x (R * c ^ k) = (closedBall x 0)ᶜ := by
  ext y
  simp only [Set.mem_iUnion, Set.mem_sdiff, mem_ball, not_lt, Set.mem_compl_iff, mem_closedBall,
    not_le]
  constructor
  · rintro ⟨k, -, hk⟩
    exact (mul_pos hR (zpow_pos (zero_lt_one.trans hc) k)).trans_le hk
  · intro hy
    obtain ⟨k, hk₁, hk₂⟩ := exists_mem_Ico_zpow (div_pos hy hR) hc
    refine ⟨k, ?_, ?_⟩
    · rwa [div_lt_iff₀ hR, mul_comm] at hk₂
    · rwa [le_div_iff₀ hR, mul_comm] at hk₁

open Filter Topology in
/-- Eventually along `l ×ˢ 𝓝 x`, a radius sequence tending to zero plus the distance to `x`
stays below any positive `r`. -/
theorem Metric.eventually_add_dist_lt_of_tendsto_zero {ι X : Type*} [PseudoMetricSpace X] {x : X}
    {l : Filter ι} {r : ℝ} (hr : 0 < r) {rho : ι → ℝ} (hrho : Tendsto rho l (𝓝 0)) :
    ∀ᶠ p : ι × X in l ×ˢ 𝓝 x, rho p.1 + dist p.2 x < r := by
  have ht : Tendsto (fun p : ι × X => rho p.1 + dist p.2 x)
      (l ×ˢ 𝓝 x) (𝓝 (0 + dist x x)) :=
    (hrho.comp tendsto_fst).add
      (((continuous_id.dist continuous_const).tendsto x).comp tendsto_snd)
  have ht0 : Tendsto (fun p : ι × X => rho p.1 + dist p.2 x)
      (l ×ˢ 𝓝 x) (𝓝 0) := by simpa only [dist_self, zero_add] using ht
  exact (tendsto_order.1 ht0).2 r hr

/-- On the real line, the extended distance from `b` to `a ≤ b` is `b - a`. -/
theorem Real.edist_eq_ofReal_sub_of_le {a b : ℝ} (h : a ≤ b) :
    edist b a = ENNReal.ofReal (b - a) := by
  rw [edist_dist, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr h)]
