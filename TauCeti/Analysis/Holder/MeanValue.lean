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
import Mathlib.Analysis.Normed.Affine.Convex

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
* `TauCeti.holderOnWith_ball_of_norm_le_rpow_of_norm_fderiv_le_rpow`: a function vanishing at `0`
  with weighted bounds `‖f z‖ ≤ A ‖z‖ ^ α` and `‖Df z‖ ≤ B ‖z‖ ^ (α - 1)` on a punctured ball is
  `α`-Hölder on the ball.
* `ContDiffOn.exists_holderOnWith`: a function `C¹` on a compact convex set is Hölder there.
* `ContDiffOn.exists_holderOnWith_comp`: a map `C¹` on a compact convex set, after a Hölder map
  with values in that set, is Hölder with the same exponent.
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

/-- The near-diagonal case of `holderOnWith_ball_of_norm_le_rpow_of_norm_fderiv_le_rpow`: if
`‖x - y‖ ≤ ‖x‖ / 2`, the segment from `x` to `y` stays at distance at least `‖x - y‖` from `0`,
where the derivative is at most `B ‖x - y‖ ^ (α - 1)`. -/
private theorem norm_sub_le_of_norm_fderiv_le_rpow_of_near {f : E → F} {α r B : ℝ} (hα : α ≤ 1)
    (hB : 0 ≤ B) (hf : ∀ z ∈ ball (0 : E) r, z ≠ 0 → DifferentiableAt ℝ f z)
    (hf1 : ∀ z ∈ ball (0 : E) r, z ≠ 0 → ‖fderiv ℝ f z‖ ≤ B * ‖z‖ ^ (α - 1))
    {x y : E} (hx : x ∈ ball (0 : E) r) (hy : y ∈ ball (0 : E) r)
    (hxy : ‖x - y‖ ≤ ‖x‖ / 2) (hne : x ≠ y) : ‖f x - f y‖ ≤ B * ‖x - y‖ ^ α := by
  have hd : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  -- every point of the segment is in the ball and at distance at least `‖x - y‖` from `0`
  have hseg : ∀ z ∈ segment ℝ x y, z ∈ ball (0 : E) r ∧ z ≠ 0 ∧ ‖x - y‖ ≤ ‖z‖ := by
    intro z hz
    have h1 := dist_add_dist_of_mem_segment hz
    rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at h1
    have h2 := norm_sub_norm_le x (x - z)
    rw [sub_sub_cancel] at h2
    have h3 : ‖x - y‖ ≤ ‖z‖ := by linarith [norm_nonneg (z - y)]
    exact ⟨(convex_ball (0 : E) r).segment_subset hx hy hz, norm_pos_iff.1 (hd.trans_le h3), h3⟩
  have hmvt := (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le
    (fun z hz ↦ hf z (hseg z hz).1 (hseg z hz).2.1)
    (fun z hz ↦ (hf1 z (hseg z hz).1 (hseg z hz).2.1).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hd (hseg z hz).2.2 (by linarith)) hB))
    (right_mem_segment ℝ x y) (left_mem_segment ℝ x y)
  calc ‖f x - f y‖ ≤ B * ‖x - y‖ ^ (α - 1) * ‖x - y‖ := hmvt
    _ = B * ‖x - y‖ ^ α := by rw [Real.rpow_sub_one hd.ne', mul_assoc, div_mul_cancel₀ _ hd.ne']

/-- **Hölder bound from weighted bounds at a point.** A function vanishing at `0` and
differentiable on the punctured ball `ball 0 r \ {0}`, with `‖f z‖ ≤ A ‖z‖ ^ α` and
`‖Df z‖ ≤ B ‖z‖ ^ (α - 1)` there, is `α`-Hölder on `ball 0 r` with constant `B + 4 A`, for every
`α ≤ 1`. Near the diagonal, `‖x - y‖ ≤ ‖x‖ / 2`, the mean value inequality along the segment from
`x` to `y` gives `‖f x - f y‖ ≤ B ‖x - y‖ ^ α`; away from it, `‖x‖ < 2 ‖x - y‖` and the bound on
`f` does. -/
theorem holderOnWith_ball_of_norm_le_rpow_of_norm_fderiv_le_rpow {f : E → F} {r : ℝ}
    {A B α : ℝ≥0} (hα : α ≤ 1) (h0 : f 0 = 0)
    (hf : ∀ z ∈ ball (0 : E) r, z ≠ 0 → DifferentiableAt ℝ f z)
    (hf0 : ∀ z ∈ ball (0 : E) r, z ≠ 0 → ‖f z‖ ≤ A * ‖z‖ ^ (α : ℝ))
    (hf1 : ∀ z ∈ ball (0 : E) r, z ≠ 0 → ‖fderiv ℝ f z‖ ≤ B * ‖z‖ ^ ((α : ℝ) - 1)) :
    HolderOnWith (B + 4 * A) α f (ball 0 r) := by
  have hα' : (α : ℝ) ≤ 1 := by exact_mod_cast hα
  have hfA : ∀ z ∈ ball (0 : E) r, ‖f z‖ ≤ A * ‖z‖ ^ (α : ℝ) := fun z hz ↦ by
    rcases eq_or_ne z 0 with rfl | hz0
    · simpa [h0] using mul_nonneg A.coe_nonneg (Real.rpow_nonneg le_rfl _)
    · exact hf0 z hz hz0
  refine HolderOnWith.of_dist_le ?_
  push_cast
  -- by symmetry, it suffices to treat `‖y‖ ≤ ‖x‖`
  suffices H : ∀ x ∈ ball (0 : E) r, ∀ y ∈ ball (0 : E) r, ‖y‖ ≤ ‖x‖ →
      ‖f x - f y‖ ≤ (B + 4 * A) * ‖x - y‖ ^ (α : ℝ) by
    intro x hx y hy
    simp only [dist_eq_norm]
    rcases le_total ‖y‖ ‖x‖ with h | h
    · exact H x hx y hy h
    · rw [norm_sub_rev (f x), norm_sub_rev x]
      exact H y hy x hx h
  intro x hx y hy hyx
  have hpow : 0 ≤ ‖x - y‖ ^ (α : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
  have hA := A.coe_nonneg
  have hB := B.coe_nonneg
  rcases eq_or_ne x y with rfl | hne
  · simpa using mul_nonneg (by positivity : (0 : ℝ) ≤ B + 4 * A) hpow
  rcases le_or_gt ‖x - y‖ (‖x‖ / 2) with hxy | hxy
  · have := norm_sub_le_of_norm_fderiv_le_rpow_of_near hα' hB hf hf1 hx hy hxy hne
    nlinarith
  · -- far from the diagonal both values are small: `‖x‖ < 2 ‖x - y‖`
    have h2 : (2 : ℝ) ^ (α : ℝ) ≤ 2 := by
      simpa using Real.rpow_le_rpow_of_exponent_le one_le_two hα'
    have hxα : ‖x‖ ^ (α : ℝ) ≤ 2 * ‖x - y‖ ^ (α : ℝ) := by
      calc ‖x‖ ^ (α : ℝ) ≤ (2 * ‖x - y‖) ^ (α : ℝ) :=
            Real.rpow_le_rpow (norm_nonneg _) (by linarith) α.coe_nonneg
        _ = 2 ^ (α : ℝ) * ‖x - y‖ ^ (α : ℝ) := Real.mul_rpow zero_le_two (norm_nonneg _)
        _ ≤ 2 * ‖x - y‖ ^ (α : ℝ) := mul_le_mul_of_nonneg_right h2 hpow
    have hyα : ‖y‖ ^ (α : ℝ) ≤ ‖x‖ ^ (α : ℝ) :=
      Real.rpow_le_rpow (norm_nonneg _) hyx α.coe_nonneg
    calc ‖f x - f y‖ ≤ ‖f x‖ + ‖f y‖ := norm_sub_le _ _
      _ ≤ A * ‖x‖ ^ (α : ℝ) + A * ‖y‖ ^ (α : ℝ) := add_le_add (hfA x hx) (hfA y hy)
      _ ≤ (B + 4 * A) * ‖x - y‖ ^ (α : ℝ) := by nlinarith

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

/-- A `C¹` map after an `r`-Hölder map is `r`-Hölder: if `f` is `r`-Hölder on `s` with values in
a compact convex set `t`, then `g ∘ f` is `r`-Hölder on `s` for every map `g` that is `C¹` on `t`,
since `g` is Lipschitz there. -/
theorem ContDiffOn.exists_holderOnWith_comp {X E F : Type*} [PseudoEMetricSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {g : E → F}
    {t : Set E} (hg : ContDiffOn ℝ 1 g t) (ht : Convex ℝ t) (ht' : IsCompact t) {f : X → E}
    {s : Set X} {C r : ℝ≥0} (hf : HolderOnWith C r f s) (hft : MapsTo f s t) :
    ∃ K, HolderOnWith K r (g ∘ f) s := by
  obtain ⟨Kg, hKg⟩ := hg.exists_lipschitzOnWith one_ne_zero ht ht'
  have h := (holderOnWith_one.2 hKg).comp hf hft
  rw [one_mul] at h
  exact ⟨_, h⟩
