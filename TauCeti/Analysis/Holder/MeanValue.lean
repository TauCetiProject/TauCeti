/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import TauCeti.Topology.MetricSpace.Holder

/-!
# Hölder bounds from bounds on a function and its derivative

A function on a real normed space which is bounded by `N₀`, with derivative bounded by `N₁`, is
`α`-Hölder for every `α ≤ 1`. By the mean value inequality it is `N₁`-Lipschitz on every convex
set where the derivative bound holds, which is used between nearby points, and the bound `N₀`
controls its oscillation between distant points (`HolderOnWith.of_le_of_dist_le`).

## Main declarations

* `TauCeti.holderWith_of_norm_le_of_norm_fderiv_le`: on the whole space, the Hölder constant is
  `N₁ + 2 N₀`.
* `TauCeti.holderOnWith_thickening_of_norm_fderiv_le`: if the bounds hold on an open set containing
  the `2δ`-thickening of a set `K`, the function is Hölder on the `δ`-thickening of `K`.
-/

public section

open Metric Set
open scoped NNReal

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- A differentiable function on the whole space bounded by `N₀`, with derivative bounded by `N₁`,
is `α`-Hölder with constant `N₁ + 2 N₀` for every `α ≤ 1`: it is `N₁`-Lipschitz, which is used at
distances less than `1`. -/
theorem holderWith_of_norm_le_of_norm_fderiv_le {g : E → F} {N₀ N₁ α : ℝ≥0} (hα : α ≤ 1)
    (hg : Differentiable ℝ g) (hg0 : ∀ x, ‖g x‖ ≤ N₀) (hg1 : ∀ x, ‖fderiv ℝ g x‖ ≤ N₁) :
    HolderWith (N₁ + 2 * N₀) α g := by
  have hL : LipschitzWith N₁ g := lipschitzWith_of_nnnorm_fderiv_le hg fun x => by
    rw [← NNReal.coe_le_coe, coe_nnnorm]
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
