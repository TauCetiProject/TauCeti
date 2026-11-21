/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.MeanValue
public import TauCeti.Topology.MetricSpace.Holder

import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Hölder bounds from bounds on a function and its derivative

A function on a real normed space which is bounded by `N₀`, with derivative bounded by `N₁`, is
`α`-Hölder for every `α ≤ 1`. By the mean value inequality it is `N₁`-Lipschitz on every convex
set where the derivative bound holds, which is used between nearby points, and the bound `N₀`
controls its oscillation between distant points (`HolderOnWith.of_le_of_dist_le`).

Conversely, a Hölder bound with exponent `r > 1` forces the derivative to vanish: the increment
`f y - f x` is `O(‖y - x‖ʳ)`, which is `o(‖y - x‖)`. So on a preconnected open set the only such
functions are the constants, which is why Hölder exponents are taken in `(0, 1]`.

## Main declarations

* `TauCeti.holderWith_of_norm_le_of_norm_fderiv_le`: on the whole space, the Hölder constant is
  `N₁ + 2 N₀`.
* `TauCeti.holderOnWith_thickening_of_norm_fderiv_le`: if the bounds hold on an open set containing
  the `2δ`-thickening of a set `K`, the function is Hölder on the `δ`-thickening of `K`.
* `HolderOnWith.hasFDerivAt_zero_of_one_lt`: a function `r`-Hölder near a point, with `r > 1`, has
  derivative zero there.
* `HolderOnWith.eq_of_one_lt`: a function `r`-Hölder on a preconnected open set, with `r > 1`, is
  constant there.
* `ContDiffOn.exists_holderOnWith`: a function `C¹` on a compact convex set is Hölder there.
-/

public section

open Filter Metric Set
open scoped NNReal Topology

section OneLt

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A function that is `r`-Hölder on a neighbourhood of `x`, with `r > 1`, has derivative zero at
`x`: its increments are `O(‖y - x‖ʳ)`, hence `o(‖y - x‖)`. -/
theorem HolderOnWith.hasFDerivAt_zero_of_one_lt {f : E → F} {C r : ℝ≥0} {s : Set E} {x : E}
    (hf : HolderOnWith C r f s) (hr : 1 < r) (hs : s ∈ 𝓝 x) :
    HasFDerivAt f (0 : E →L[𝕜] F) x := by
  have hr' : (0 : ℝ) < r - 1 := by
    rw [sub_pos]
    exact_mod_cast hr
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  simp only [zero_apply, sub_zero]
  refine Asymptotics.IsLittleO.of_bound fun ε hε ↦ ?_
  -- The factor `C ‖h‖^(r - 1)` tends to `0` with `h`.
  have hlim : Tendsto (fun h : E ↦ (C : ℝ) * ‖h‖ ^ ((r : ℝ) - 1)) (𝓝 0) (𝓝 0) := by
    have h := ((continuous_norm.tendsto (0 : E)).rpow_const (p := (r : ℝ) - 1)
      (Or.inr hr'.le)).const_mul (C : ℝ)
    rwa [norm_zero, Real.zero_rpow hr'.ne', mul_zero] at h
  have hs' : ∀ᶠ h : E in 𝓝 0, x + h ∈ s := by
    have h := (continuous_const_add x).tendsto (0 : E)
    rw [add_zero] at h
    exact h hs
  filter_upwards [hs', hlim.eventually (ge_mem_nhds hε)] with h hxh hC
  calc ‖f (x + h) - f x‖ = dist (f (x + h)) (f x) := (dist_eq_norm _ _).symm
    _ ≤ C * dist (x + h) x ^ (r : ℝ) := hf.dist_le hxh (mem_of_mem_nhds hs)
    _ = C * ‖h‖ ^ ((r : ℝ) - 1) * ‖h‖ := by
        rw [dist_eq_norm, add_sub_cancel_left, mul_assoc,
          ← Real.rpow_add_one' (norm_nonneg h) (by linarith : (0 : ℝ) < r - 1 + 1).ne',
          sub_add_cancel]
    _ ≤ ε * ‖h‖ := mul_le_mul_of_nonneg_right hC (norm_nonneg h)

end OneLt

/-- **Hölder exponents above one.** A function that is `r`-Hölder on a preconnected open set, with
`r > 1`, is constant there. -/
theorem HolderOnWith.eq_of_one_lt {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {C r : ℝ≥0} {s : Set E}
    (hf : HolderOnWith C r f s) (hr : 1 < r) (hs : IsOpen s) (hs' : IsPreconnected s) {x y : E}
    (hx : x ∈ s) (hy : y ∈ s) : f x = f y :=
  hs.is_const_of_fderiv_eq_zero (𝕜 := ℝ) hs'
    (fun _ hz ↦ (hf.hasFDerivAt_zero_of_one_lt hr (hs.mem_nhds hz)).differentiableAt
      |>.differentiableWithinAt)
    (fun _ hz ↦ (hf.hasFDerivAt_zero_of_one_lt hr (hs.mem_nhds hz)).fderiv) hx hy

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- A differentiable function on the whole space bounded by `N₀`, with derivative bounded by `N₁`,
is `α`-Hölder with constant `N₁ + 2 N₀` for every `α ≤ 1`: it is `N₁`-Lipschitz, which is used at
distances less than `1`. -/
theorem holderWith_of_norm_le_of_norm_fderiv_le {g : E → F} {N₀ N₁ α : ℝ≥0} (hα : α ≤ 1)
    (hg : Differentiable ℝ g) (hg0 : ∀ x, ‖g x‖ ≤ N₀) (hg1 : ∀ x, ‖fderiv ℝ g x‖ ≤ N₁) :
    HolderWith (N₁ + 2 * N₀) α g := by
  have hL : LipschitzWith N₁ g := lipschitzWith_of_nnNorm_fderiv_le hg fun x => by
    rw [← NNReal.coe_le_coe, coe_nnNorm]
    exact hg1 x
  have h := HolderOnWith.of_le_of_dist_le (s := univ) (δ := 1) (D := 2 * N₀)
    (fun x _ y _ _ => (holderWith_one.2 hL).dist_le x y) (fun x _ y _ => ?_) hα one_pos
  · simpa only [NNReal.one_rpow, mul_one, holderOnWith_univ] using h
  · push_cast
    linarith [dist_le_norm_add_norm (g x) (g y), hg0 x, hg0 y]

/-- A function bounded by `N₀`, with derivative bounded by `N₁`, on an open set containing the
`2δ`-thickening of `K` is `α`-Hölder on the `δ`-thickening of `K` for every `α ≤ 1`, with constant
`N₁ δ^(1 - α) + 2 N₀ δ^(-α)`: nearby points of the `δ`-thickening lie in a ball of radius `δ`
contained in the `2δ`-thickening, on which the function is `N₁`-Lipschitz. -/
theorem holderOnWith_thickening_of_norm_fderiv_le {Ω K : Set E} {g : E → F} {δ N₀ N₁ α : ℝ≥0}
    (hδ : 0 < δ) (hα : α ≤ 1) (hΩ : IsOpen Ω) (hKΩ : thickening (2 * δ) K ⊆ Ω)
    (hg : DifferentiableOn ℝ g Ω) (hg0 : ∀ x ∈ Ω, ‖g x‖ ≤ N₀)
    (hg1 : ∀ x ∈ Ω, ‖fderiv ℝ g x‖ ≤ N₁) :
    HolderOnWith (N₁ * δ ^ (1 - (α : ℝ)) + 2 * N₀ * δ ^ (-(α : ℝ))) α g (thickening δ K) := by
  have h := HolderOnWith.of_le_of_dist_le (f := g) (s := thickening δ K) (β := 1) (K := N₁)
    (D := 2 * N₀) (fun x hx y _ hxy => ?_) (fun x hx y hy => ?_) hα hδ
  · simpa only [NNReal.coe_one] using h
  · -- The ball `B(x, δ)` is convex and lies in `Ω`, where `‖Dg‖ ≤ N₁`.
    have hball : ball x δ ⊆ Ω := fun z hz => hKΩ <| by
      rw [two_mul]
      exact thickening_thickening_subset _ _ K (ball_subset_thickening hx _ hz)
    have hy : y ∈ ball x δ := by rw [mem_ball, dist_comm]; exact hxy
    rw [NNReal.coe_one, Real.rpow_one, dist_comm (g x), dist_comm x y, dist_eq_norm,
      dist_eq_norm]
    exact (convex_ball x δ).norm_image_sub_le_of_norm_fderiv_le
      (fun z hz => hg.differentiableAt (hΩ.mem_nhds (hball hz))) (fun z hz => hg1 z (hball hz))
      (mem_ball_self (by exact_mod_cast hδ)) hy
  · have hU : thickening (δ : ℝ) K ⊆ Ω :=
      (thickening_mono (by linarith [δ.coe_nonneg]) K).trans hKΩ
    push_cast
    linarith [dist_le_norm_add_norm (g x) (g y), hg0 x (hU hx), hg0 y (hU hy)]

end TauCeti

/-- A function that is `C¹` on a compact convex set is `α`-Hölder there for every `α ≤ 1`: it is
Lipschitz and bounded on that set. -/
theorem ContDiffOn.exists_holderOnWith {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {s : Set E} {g : E → F} (hg : ContDiffOn ℝ 1 g s)
    (hs : Convex ℝ s) (hs' : IsCompact s) {α : ℝ≥0} (hα : α ≤ 1) :
    ∃ C, HolderOnWith C α g s := by
  obtain ⟨K, hK⟩ := hg.exists_lipschitzOnWith one_ne_zero hs hs'
  obtain ⟨M, hM⟩ := hs'.exists_bound_of_continuousOn hg.continuousOn
  exact ⟨_, hK.holderOnWith_of_norm_le (M := M.toNNReal)
    (fun x hx ↦ (hM x hx).trans (Real.le_coe_toNNReal M)) hα⟩
