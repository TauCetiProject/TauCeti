/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

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

The bounded transform `dist x y / (1 + dist x y)` satisfies the triangle inequality
(`Metric.dist_div_one_add_dist_le`).

On the real line, the extended distance from `b` to `a ≤ b` is `b - a`
(`Real.edist_eq_ofReal_sub_of_le`).

In a Hausdorff pseudometric space, if `f → a` and `g → b` along a nontrivial filter `l` with
`dist (g z) (f z) ≤ dist (f z) a` eventually, then `a = b`
(`Filter.Tendsto.eq_of_eventually_dist_le`).

The metric entourages `{p | dist p.1 p.2 < ε}` and `{p | dist p.1 p.2 ≤ ε}` grow with `ε`
(`Metric.monotone_ofPred_dist_lt`, `Metric.monotone_ofPred_dist_le`).
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

/-- The bounded transform `d / (1 + d)` of a pseudometric satisfies the triangle inequality. -/
theorem Metric.dist_div_one_add_dist_le {X : Type*} [PseudoMetricSpace X] (a b c : X) :
    dist a c / (1 + dist a c) ≤
      dist a b / (1 + dist a b) + dist b c / (1 + dist b c) := by
  have hab : 0 ≤ dist a b := dist_nonneg
  have hbc : 0 ≤ dist b c := dist_nonneg
  have ht := dist_triangle a b c
  have hm : dist a c / (1 + dist a c) ≤
      (dist a b + dist b c) / (1 + (dist a b + dist b c)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [dist_nonneg (x := a) (y := c)]
  refine hm.trans ?_
  rw [add_div]
  exact add_le_add
    (div_le_div_of_nonneg_left hab (by positivity) (by linarith))
    (div_le_div_of_nonneg_left hbc (by positivity) (by linarith))

open Filter Topology in
/-- If `f` tends to `a` and `g` tends to `b` along a nontrivial filter `l` in a Hausdorff
pseudometric space, and eventually `dist (g z) (f z) ≤ dist (f z) a`, then `a = b`. -/
theorem Filter.Tendsto.eq_of_eventually_dist_le {α β : Type*} [PseudoMetricSpace β] [T2Space β]
    {l : Filter α} [l.NeBot] {f g : α → β} {a b : β} (hf : Tendsto f l (𝓝 a))
    (hg : Tendsto g l (𝓝 b)) (h : ∀ᶠ z in l, dist (g z) (f z) ≤ dist (f z) a) : a = b :=
  tendsto_nhds_unique
    (hf.congr_dist (squeeze_zero' (.of_forall fun _ ↦ dist_nonneg)
      (h.mono fun z hz ↦ dist_comm (g z) (f z) ▸ hz) (tendsto_iff_dist_tendsto_zero.1 hf)))
    hg

/-- The metric entourages `{p | dist p.1 p.2 < ε}` grow with `ε`. -/
theorem Metric.monotone_ofPred_dist_lt {X : Type*} [PseudoMetricSpace X] :
    Monotone fun ε : ℝ ↦ {p : X × X | dist p.1 p.2 < ε} :=
  fun _ _ h _ hp ↦ lt_of_lt_of_le hp h

/-- The metric entourages `{p | dist p.1 p.2 ≤ ε}` grow with `ε`. -/
theorem Metric.monotone_ofPred_dist_le {X : Type*} [PseudoMetricSpace X] :
    Monotone fun ε : ℝ ↦ {p : X × X | dist p.1 p.2 ≤ ε} :=
  fun _ _ h _ hp ↦ le_trans hp h
