/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Lipschitz
import TauCeti.Algebra.Order.Field.Basic

/-!
# Basic Lipschitz estimates

This file collects elementary `LipschitzWith` facts and bounded-gauge estimates:

* The shifted positive part `t ↦ max (t - k) 0` is `1`-Lipschitz on the real line.
* The plateau `x ↦ max (min t (ρ - dist x x₀)) 0` is a `1`-Lipschitz function with values in
  `[0, t]`, equal to `t` near `x₀` and vanishing at distance at least `ρ` from `x₀`.
* Pointwise infima `x ↦ sInf ((F x) '' S)` of uniformly `K`-Lipschitz families bounded below at
  each point are `K`-Lipschitz.
* A `K`-Lipschitz map with `1 ≤ K` scales the bounded-metric gauge `d / (1 + d)` by at most `K`,
  and a `K`-Lipschitz binary map on a product pseudometric space bounds the output gauge by `K`
  times the sum of the component gauges.
* The positive part `ENNReal.ofReal ∘ h` of a real `K`-Lipschitz function satisfies the extended
  Lipschitz bound `ENNReal.ofReal (h x) ≤ ENNReal.ofReal (h y) + K * edist x y`.

## Main results

* `TauCeti.lipschitzWith_max_sub_const_zero`: the shifted positive part is `1`-Lipschitz.
* `TauCeti.exists_lipschitzWith_one_plateau`: a `1`-Lipschitz plateau of height `t ≤ 1` about
  a point, vanishing off a ball.
* `TauCeti.lipschitzWith_sInf_image`: pointwise infimum over an index set `S` preserves a uniform
  Lipschitz constant `K` when each slice `(F x) '' S` is bounded below.
* `LipschitzWith.dist_div_one_add_dist_le_mul`: bounded-gauge estimate for a `K`-Lipschitz map
  with `1 ≤ K`.
* `LipschitzWith.dist_div_one_add_dist_prod_le`: bounded-gauge estimate for a `K`-Lipschitz binary
  map `α × β → γ` with `1 ≤ K`.
* `LipschitzWith.ofReal_le_ofReal_add_mul_edist`: the extended Lipschitz bound for the positive
  part of a real Lipschitz function.

## References

* H. Federer, *Geometric Measure Theory*, Springer (1969), Section 2.2.7.
-/

public section

open scoped NNReal

namespace TauCeti

/-- The shifted positive part `t ↦ max (t - k) 0` is `1`-Lipschitz on the real line. -/
theorem lipschitzWith_max_sub_const_zero (k : ℝ) :
    LipschitzWith 1 (fun t : ℝ => max (t - k) 0) :=
  LipschitzWith.of_dist_le_mul fun x y => by
    simpa only [NNReal.coe_one, one_mul, Real.dist_eq, sub_sub_sub_cancel_right] using
      abs_max_sub_max_le_abs (x - k) (y - k) 0

/-- **A Lipschitz plateau.** For `0 ≤ t ≤ 1`, a centre `x₀` and a radius `ρ`, there is a
`1`-Lipschitz function `g` with values in `[0, t]`, equal to `t` within `ρ - t` of `x₀` and to `0`
at distance at least `ρ` from `x₀`, namely `max (min t (ρ - dist x x₀)) 0`. It is a test function
for the bounded-Lipschitz distance that separates a ball from the complement of a larger one. -/
theorem exists_lipschitzWith_one_plateau {X : Type*} [PseudoMetricSpace X] {t : ℝ} (ht₀ : 0 ≤ t)
    (ht₁ : t ≤ 1) (x₀ : X) (ρ : ℝ) :
    ∃ g : X → ℝ, LipschitzWith 1 g ∧ (∀ x, 0 ≤ g x ∧ g x ≤ t) ∧ (∀ x, |g x| ≤ 1) ∧
      (∀ x, dist x x₀ ≤ ρ - t → g x = t) ∧ ∀ x, ρ ≤ dist x x₀ → g x = 0 := by
  refine ⟨fun x ↦ max (min t (ρ - dist x x₀)) 0, ?_, fun x ↦ ⟨le_max_right _ _,
    max_le (min_le_left _ _) ht₀⟩, fun x ↦ ?_, fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · refine ((LipschitzWith.of_dist_le_mul fun x y ↦ ?_).const_min t).max_const 0
    rw [Real.dist_eq, sub_sub_sub_cancel_left, NNReal.coe_one, one_mul, abs_sub_comm]
    exact abs_dist_sub_le x y x₀
  · rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le ((min_le_left _ _).trans ht₁) zero_le_one
  · dsimp only
    rw [min_eq_left (by linarith), max_eq_left ht₀]
  · exact max_eq_right ((min_le_right _ _).trans (by linarith))

/-- Pointwise infimum over `S` preserves a uniform Lipschitz constant `K` when each slice is
bounded below. -/
theorem lipschitzWith_sInf_image {α ι : Type*} [PseudoMetricSpace α] {S : Set ι}
    {F : α → ι → ℝ} {K : NNReal} (hbdd : ∀ x, BddBelow ((F x) '' S))
    (hlip : ∀ i ∈ S, LipschitzWith K (fun x ↦ F x i)) :
    LipschitzWith K (fun x ↦ sInf ((F x) '' S)) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  rw [Real.dist_eq]
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp only [Set.image_empty, Real.sInf_empty, sub_self, abs_zero]; positivity
  · have hle (u v : α) : sInf ((F u) '' S) - (K : ℝ) * dist u v ≤ sInf ((F v) '' S) := by
      refine le_csInf (hS.image _) ?_
      rintro _ ⟨i, hi, rfl⟩
      have hd : F u i - F v i ≤ (K : ℝ) * dist u v := (le_abs_self _).trans <| by
        simpa only [Real.dist_eq] using (hlip i hi).dist_le_mul u v
      linarith [csInf_le (hbdd u) ⟨i, hi, rfl⟩]
    rw [abs_sub_le_iff]
    exact ⟨by linarith [hle x y], by linarith [dist_comm x y ▸ hle y x]⟩

end TauCeti

namespace LipschitzWith

/-- For a `K`-Lipschitz map `f : α → β` with `1 ≤ K`, the bounded-metric gauge `d / (1 + d)`
satisfies `dist (f x) (f y) / (1 + dist (f x) (f y)) ≤ K * (dist x y / (1 + dist x y))`. -/
theorem dist_div_one_add_dist_le_mul {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    {K : ℝ≥0} {f : α → β} (hf : LipschitzWith K f) (hK : 1 ≤ K) (x y : α) :
    dist (f x) (f y) / (1 + dist (f x) (f y)) ≤
      (K : ℝ) * (dist x y / (1 + dist x y)) :=
  (TauCeti.div_one_add_mono dist_nonneg (hf.dist_le_mul x y)).trans
    (TauCeti.mul_div_one_add_mul_le (NNReal.one_le_coe.mpr hK) dist_nonneg)

/-- For a `K`-Lipschitz binary map `f : α × β → γ` with `1 ≤ K`, the bounded-metric gauge of `f`
is bounded by `K` times the sum of the component gauges. -/
theorem dist_div_one_add_dist_prod_le {α β γ : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    [PseudoMetricSpace γ] {K : ℝ≥0} {f : α × β → γ} (hf : LipschitzWith K f) (hK : 1 ≤ K)
    (p q : α × β) :
    dist (f p) (f q) / (1 + dist (f p) (f q)) ≤
      (K : ℝ) * (dist p.1 q.1 / (1 + dist p.1 q.1)) +
        (K : ℝ) * (dist p.2 q.2 / (1 + dist p.2 q.2)) := by
  calc dist (f p) (f q) / (1 + dist (f p) (f q))
      ≤ (K : ℝ) * (dist p q / (1 + dist p q)) :=
        hf.dist_div_one_add_dist_le_mul hK p q
    _ ≤ (K : ℝ) * (dist p.1 q.1 / (1 + dist p.1 q.1) +
          dist p.2 q.2 / (1 + dist p.2 q.2)) := by
        refine mul_le_mul_of_nonneg_left ?_ K.coe_nonneg
        rw [Prod.dist_eq]
        rcases le_total (dist p.1 q.1) (dist p.2 q.2) with h | h
        · rw [max_eq_right h]
          exact le_add_of_nonneg_left (TauCeti.div_one_add_nonneg dist_nonneg)
        · rw [max_eq_left h]
          exact le_add_of_nonneg_right (TauCeti.div_one_add_nonneg dist_nonneg)
    _ = (K : ℝ) * (dist p.1 q.1 / (1 + dist p.1 q.1)) +
          (K : ℝ) * (dist p.2 q.2 / (1 + dist p.2 q.2)) := mul_add _ _ _

/-- The positive part of a real `K`-Lipschitz function satisfies the extended Lipschitz bound
`ENNReal.ofReal (h x) ≤ ENNReal.ofReal (h y) + K * edist x y`. -/
theorem ofReal_le_ofReal_add_mul_edist {α : Type*} [PseudoMetricSpace α] {K : ℝ≥0} {h : α → ℝ}
    (hh : LipschitzWith K h) (x y : α) :
    ENNReal.ofReal (h x) ≤ ENNReal.ofReal (h y) + K * edist x y :=
  calc ENNReal.ofReal (h x) ≤ ENNReal.ofReal (h y + K * dist x y) :=
        ENNReal.ofReal_le_ofReal (hh.le_add_mul x y)
    _ ≤ ENNReal.ofReal (h y) + K * edist x y := by
      rw [edist_dist, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul K.coe_nonneg]
      exact ENNReal.ofReal_add_le

end LipschitzWith
