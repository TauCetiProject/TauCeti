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

## Main declarations

* `TauCeti.holderWith_of_norm_le_of_norm_fderiv_le`: on the whole space, the Hölder constant is
  `N₁ + 2 N₀`.
* `TauCeti.holderOnWith_thickening_of_norm_fderiv_le`: if the bounds hold on an open set containing
  the `2δ`-thickening of a set `K`, the function is Hölder on the `δ`-thickening of `K`.
* `TauCeti.holderOnWith_ball_of_norm_fderiv_le`: on a ball `B_R`, the derivative bound `N₁` alone
  gives the Hölder constant `N₁ (2R)^(1 - α)`.
* `TauCeti.holderOnWith_fderiv_ball_of_norm_iteratedFDeriv_two_le`: on a ball `B_R`, the
  derivative of a `C²` function with second derivative bounded by `N₂` is Hölder with constant
  `N₂ (2R)^(1 - α)`.
* `ContDiffOn.exists_holderOnWith`: a function `C¹` on a compact convex set is Hölder there.
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

/-- A function differentiable on the ball `B_R`, with derivative bounded by `N` there, is `α`-Hölder
on `B_R` with constant `N (2R)^(1 - α)` for every `α ≤ 1`: it is `N`-Lipschitz on the convex set
`B_R`, whose diameter is at most `2R`. -/
theorem holderOnWith_ball_of_norm_fderiv_le {g : E → F} {x₀ : E} {R : ℝ} {N α : ℝ≥0}
    (hα : α ≤ 1) (hg : DifferentiableOn ℝ g (ball x₀ R))
    (hN : ∀ x ∈ ball x₀ R, ‖fderiv ℝ g x‖ ≤ N) :
    HolderOnWith (N * (2 * R).toNNReal ^ ((1 : ℝ) - α)) α g (ball x₀ R) := by
  have hA : ∀ x ∈ ball x₀ R, ∀ y ∈ ball x₀ R, edist x y ≤ (2 * R).toNNReal := by
    intro x hx y hy
    rw [edist_dist]
    refine ENNReal.ofReal_le_ofReal ?_
    linarith [dist_triangle_right x y x₀, mem_ball.1 hx, mem_ball.1 hy]
  have hL : LipschitzOnWith N g (ball x₀ R) :=
    (convex_ball x₀ R).lipschitzOnWith_of_nnNorm_fderiv_le
      (fun x hx => hg.differentiableAt (isOpen_ball.mem_nhds hx))
      fun x hx => by rw [← NNReal.coe_le_coe, coe_nnNorm]; exact hN x hx
  simpa using (holderOnWith_one.2 hL).of_le hA hα

/-- The derivative of a `C²` function on the ball `B_R`, with second derivative bounded by `N`
there, is `α`-Hölder on `B_R` with constant `N (2R)^(1 - α)` for every `α ≤ 1`: this is
`holderOnWith_ball_of_norm_fderiv_le` applied to `Dg`. -/
theorem holderOnWith_fderiv_ball_of_norm_iteratedFDeriv_two_le {g : E → F} {x₀ : E} {R : ℝ}
    {N α : ℝ≥0} (hα : α ≤ 1) (hg : ContDiffOn ℝ 2 g (ball x₀ R))
    (hN : ∀ x ∈ ball x₀ R, ‖iteratedFDeriv ℝ 2 g x‖ ≤ N) :
    HolderOnWith (N * (2 * R).toNNReal ^ ((1 : ℝ) - α)) α (fderiv ℝ g) (ball x₀ R) :=
  holderOnWith_ball_of_norm_fderiv_le hα
    ((hg.fderiv_of_isOpen isOpen_ball (m := 1) le_rfl).differentiableOn one_ne_zero)
    fun x hx => by rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]; exact hN x hx

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
