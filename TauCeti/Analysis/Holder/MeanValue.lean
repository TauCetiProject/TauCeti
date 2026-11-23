/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.Topology.MetricSpace.Holder

import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Topology.MetricSpace.Bounded

/-!
# Hölder bounds from bounds on a function and its derivative

A function on a real normed space which is bounded by `N₀`, with derivative bounded by `N₁`, is
`α`-Hölder for every `α ≤ 1`. By the mean value inequality it is `N₁`-Lipschitz on every convex
set where the derivative bound holds, which is used between nearby points, and the bound `N₀`
controls its oscillation between distant points (`HolderOnWith.of_le_of_dist_le`).

Conversely, a Hölder bound with exponent `r > 1` forces the derivative to vanish: the increment
`f y - f x` is `O(‖y - x‖ʳ)`, which is `o(‖y - x‖)`. So on a preconnected open set the only such
functions are the constants, which is why Hölder exponents are taken in `(0, 1]`.

A Hölder bound on the derivative along a line gives a first-order Taylor estimate along that line:
the remainder `φ (x + h • e) - φ x - h • φ' x` is `O(|h| ^ (1 + r))`.

## Main declarations

* `TauCeti.holderWith_of_norm_le_of_norm_fderiv_le`: on the whole space, the Hölder constant is
  `N₁ + 2 N₀`.
* `TauCeti.holderOnWith_thickening_of_norm_fderiv_le`: if the bounds hold on an open set containing
  the `2δ`-thickening of a set `K`, the function is Hölder on the `δ`-thickening of `K`.
* `HolderOnWith.hasFDerivAt_zero_of_one_lt`: a function `r`-Hölder near a point, with `r > 1`, has
  derivative zero there.
* `HolderOnWith.eq_of_one_lt`: a function `r`-Hölder on a preconnected open set, with `r > 1`, is
  constant there.
* `Convex.holderOnWith_of_norm_fderiv_le`: on a convex set of diameter at most `D`, the
  derivative bound `N` gives the Hölder constant `N D^(1 - α)`.
* `Convex.holderOnWith_fderiv_of_norm_iteratedFDeriv_two_le`: on a convex set of diameter at most
  `D`, the derivative of a `C²` function with second derivative bounded by `N` is Hölder with
  constant `N D^(1 - α)`.
* `Convex.holderOnWith_fderiv_apply_of_norm_iteratedFDeriv_two_le`: on a convex set of diameter
  at most `D`, the directional derivatives, along vectors of norm at most one, of a `C²` function
  with second derivative bounded by `N` are Hölder with constant `N D^(1 - α)`.
* `TauCeti.holderOnWith_ball_of_norm_fderiv_le`: on a ball `B_R`, the derivative bound `N₁` alone
  gives the Hölder constant `N₁ (2R)^(1 - α)`.
* `TauCeti.holderOnWith_fderiv_ball_of_norm_iteratedFDeriv_two_le`: on a ball `B_R`, the
  derivative of a `C²` function with second derivative bounded by `N₂` is Hölder with constant
  `N₂ (2R)^(1 - α)`.
* `TauCeti.holderOnWith_ball_of_norm_le_rpow_of_norm_fderiv_le_rpow`: a function vanishing at `0`
  with weighted bounds `‖f z‖ ≤ A ‖z‖ ^ α` and `‖Df z‖ ≤ B ‖z‖ ^ (α - 1)` on a punctured ball is
  `α`-Hölder on the ball.
* `TauCeti.holderOnWith_ball_of_norm_fderiv_le_mul_rpow`: the lemma of Hardy and Littlewood. On a
  ball `B_R(x₀)`, a derivative that may blow up at the boundary, but no faster than
  `M (R - ‖x - x₀‖)^(α - 1)` with `0 < α ≤ 1`, still makes the function `α`-Hölder on `B_R(x₀)`,
  with constant `(3 + 2 / α) M`. Two points at distance `δ` are first moved along rays to the
  ball of radius `R - δ`, which costs `(M / α) δ^α` each since the radial integral of the bound
  converges, and are then joined inside that smaller ball, where the derivative is at most
  `M δ^(α - 1)`. This reads Hölder continuity of a holomorphic function on a disc off the growth
  of its derivative.
* `ContDiffOn.exists_holderOnWith`: a function `C¹` on a compact convex set is Hölder there.
* `HolderWith.norm_sub_sub_smul_le_of_hasLineDerivAt`: the first-order Taylor estimate along a line
  for a function whose line derivative is Hölder.
* `ContDiffOn.exists_holderOnWith_comp`: a map `C¹` on a compact convex set, after a Hölder map
  with values in that set, is Hölder with the same exponent.

## References

* G. H. Hardy and J. E. Littlewood, *Some properties of fractional integrals. II*, Math. Z. **34**
  (1932), 403–439.
* P. L. Duren, *Theory of Hᵖ Spaces*, Academic Press, 1970, Chapter 5 (Hölder continuity from the
  growth of the derivative).
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

/-- **A first-order Taylor estimate along a line.** If `φ` has line derivative `φ' y` along `e` at
every point `y` and `φ'` is `r`-Hölder with constant `C`, then the remainder of the first-order
expansion of `φ` along `e` satisfies `‖φ (x + h • e) - φ x - h • φ' x‖ ≤ C ‖h • e‖ ^ r |h|`. -/
theorem HolderWith.norm_sub_sub_smul_le_of_hasLineDerivAt {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {φ φ' : E → F} {e : E}
    {C r : ℝ≥0} (hφ' : HolderWith C r φ') (hφ : ∀ y, HasLineDerivAt ℝ φ (φ' y) y e) (x : E)
    (h : ℝ) : ‖φ (x + h • e) - φ x - h • φ' x‖ ≤ C * ‖h • e‖ ^ (r : ℝ) * |h| := by
  -- `σ ↦ φ (x + σ • e) - σ • φ' x` has derivative `φ' (x + s • e) - φ' x` at `s`.
  have hψ (s : ℝ) :
      HasDerivAt (fun σ : ℝ ↦ φ (x + σ • e) - σ • φ' x) (φ' (x + s • e) - φ' x) s := by
    have h₁ : HasDerivAt (fun σ : ℝ ↦ φ ((x + s • e) + (σ - s) • e)) (φ' (x + s • e)) s :=
      HasDerivAt.comp_sub_const s s (by rw [sub_self]; exact hφ (x + s • e))
    have h₂ : (fun σ : ℝ ↦ φ ((x + s • e) + (σ - s) • e)) = fun σ ↦ φ (x + σ • e) := by
      funext σ
      rw [sub_smul, add_add_sub_cancel]
    rw [h₂] at h₁
    have h₃ := h₁.sub ((hasDerivAt_id s).smul_const (φ' x))
    simp only [id, one_smul] at h₃
    exact h₃
  have hbound : ∀ s ∈ Set.uIcc 0 h, ‖φ' (x + s • e) - φ' x‖ ≤ C * ‖h • e‖ ^ (r : ℝ) := by
    intro s hs
    have hs' : |s| ≤ |h| := by simpa using Set.abs_sub_left_of_mem_uIcc hs
    rw [← dist_eq_norm]
    refine (hφ'.dist_le _ _).trans ?_
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, norm_smul, Real.norm_eq_abs,
      Real.norm_eq_abs]
    gcongr
  have := (convex_uIcc (0 : ℝ) h).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s _ ↦ (hψ s).hasDerivWithinAt) hbound Set.left_mem_uIcc Set.right_mem_uIcc
  simpa [sub_right_comm, Real.norm_eq_abs] using this

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

/-- A function differentiable at every point of a convex set `s`, with derivative bounded by `N`
there, is `α`-Hölder on `s` with constant `N D^(1 - α)` for every `α ≤ 1`, where `D` bounds the
distances between points of `s`: it is `N`-Lipschitz on `s`. The set need not be open, so this
applies up to the flat part of the boundary of a half-ball. -/
theorem _root_.Convex.holderOnWith_of_norm_fderiv_le {g : E → F} {s : Set E} {N D α : ℝ≥0}
    (hs : Convex ℝ s) (hα : α ≤ 1) (hD : ∀ x ∈ s, ∀ y ∈ s, edist x y ≤ D)
    (hg : ∀ x ∈ s, DifferentiableAt ℝ g x) (hN : ∀ x ∈ s, ‖fderiv ℝ g x‖ ≤ N) :
    HolderOnWith (N * D ^ ((1 : ℝ) - α)) α g s := by
  have hL : LipschitzOnWith N g s :=
    hs.lipschitzOnWith_of_nnNorm_fderiv_le hg fun x hx => by
      rw [← NNReal.coe_le_coe, coe_nnNorm]; exact hN x hx
  simpa using (holderOnWith_one.2 hL).of_le hD hα

/-- The derivative of a function `C²` on an open set `U` containing a convex set `s`, with second
derivative bounded by `N` on `s`, is `α`-Hölder on `s` with constant `N D^(1 - α)` for every
`α ≤ 1`, where `D` bounds the distances between points of `s`: this is
`Convex.holderOnWith_of_norm_fderiv_le` applied to `Dg`. -/
theorem _root_.Convex.holderOnWith_fderiv_of_norm_iteratedFDeriv_two_le {g : E → F} {s U : Set E}
    {N D α : ℝ≥0} (hs : Convex ℝ s) (hα : α ≤ 1) (hD : ∀ x ∈ s, ∀ y ∈ s, edist x y ≤ D)
    (hU : IsOpen U) (hsU : s ⊆ U) (hg : ContDiffOn ℝ 2 g U)
    (hN : ∀ x ∈ s, ‖iteratedFDeriv ℝ 2 g x‖ ≤ N) :
    HolderOnWith (N * D ^ ((1 : ℝ) - α)) α (fderiv ℝ g) s :=
  hs.holderOnWith_of_norm_fderiv_le hα hD (fun x hx =>
      ((hg.fderiv_of_isOpen hU (m := 1) le_rfl).differentiableOn one_ne_zero).differentiableAt
        (hU.mem_nhds (hsU hx)))
    fun x hx => by rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]; exact hN x hx

/-- Each directional derivative, along a vector of norm at most one, of a function `C²` on an open
set `U` containing a convex set `s`, with second derivative bounded by `N` on `s`, is `α`-Hölder on
`s` with constant `N D^(1 - α)` for every `α ≤ 1`, where `D` bounds the distances between points of
`s`: evaluation at `v` is `1`-Lipschitz on `E →L[ℝ] F`. -/
theorem _root_.Convex.holderOnWith_fderiv_apply_of_norm_iteratedFDeriv_two_le {g : E → F}
    {s U : Set E} {N D α : ℝ≥0} (hs : Convex ℝ s) (hα : α ≤ 1)
    (hD : ∀ x ∈ s, ∀ y ∈ s, edist x y ≤ D) (hU : IsOpen U) (hsU : s ⊆ U)
    (hg : ContDiffOn ℝ 2 g U) (hN : ∀ x ∈ s, ‖iteratedFDeriv ℝ 2 g x‖ ≤ N) (v : E)
    (hv : ‖v‖ ≤ 1) :
    HolderOnWith (N * D ^ ((1 : ℝ) - α)) α (fun x => fderiv ℝ g x v) s := by
  have hev : LipschitzWith 1 fun L : E →L[ℝ] F => L v :=
    LipschitzWith.of_dist_le_mul fun L L' => by
      rw [dist_eq_norm, dist_eq_norm, ← sub_apply, NNReal.coe_one, one_mul]
      exact (L - L').unit_le_opNorm v hv
  have h := (holderWith_one.2 hev).comp_holderOnWith
    (hs.holderOnWith_fderiv_of_norm_iteratedFDeriv_two_le hα hD hU hsU hg hN)
  simp only [NNReal.coe_one, NNReal.rpow_one, one_mul] at h
  exact h

/-- A function differentiable on the ball `B_R`, with derivative bounded by `N` there, is `α`-Hölder
on `B_R` with constant `N (2R)^(1 - α)` for every `α ≤ 1`: it is `N`-Lipschitz on the convex set
`B_R`, whose diameter is at most `2R`. -/
theorem holderOnWith_ball_of_norm_fderiv_le {g : E → F} {x₀ : E} {R : ℝ} {N α : ℝ≥0}
    (hα : α ≤ 1) (hg : DifferentiableOn ℝ g (ball x₀ R))
    (hN : ∀ x ∈ ball x₀ R, ‖fderiv ℝ g x‖ ≤ N) :
    HolderOnWith (N * (2 * R).toNNReal ^ ((1 : ℝ) - α)) α g (ball x₀ R) :=
  (convex_ball x₀ R).holderOnWith_of_norm_fderiv_le hα
    (fun _ hx _ hy => edist_le_two_mul_of_mem_closedBall (ball_subset_closedBall hx)
      (ball_subset_closedBall hy))
    (fun _ hx => hg.differentiableAt (isOpen_ball.mem_nhds hx)) hN

/-- The derivative of a `C²` function on the ball `B_R`, with second derivative bounded by `N`
there, is `α`-Hölder on `B_R` with constant `N (2R)^(1 - α)` for every `α ≤ 1`: this is
`Convex.holderOnWith_fderiv_of_norm_iteratedFDeriv_two_le` on the ball, whose diameter is at most
`2R`. -/
theorem holderOnWith_fderiv_ball_of_norm_iteratedFDeriv_two_le {g : E → F} {x₀ : E} {R : ℝ}
    {N α : ℝ≥0} (hα : α ≤ 1) (hg : ContDiffOn ℝ 2 g (ball x₀ R))
    (hN : ∀ x ∈ ball x₀ R, ‖iteratedFDeriv ℝ 2 g x‖ ≤ N) :
    HolderOnWith (N * (2 * R).toNNReal ^ ((1 : ℝ) - α)) α (fderiv ℝ g) (ball x₀ R) :=
  (convex_ball x₀ R).holderOnWith_fderiv_of_norm_iteratedFDeriv_two_le hα
    (fun _ hx _ hy => edist_le_two_mul_of_mem_closedBall (ball_subset_closedBall hx)
      (ball_subset_closedBall hy)) isOpen_ball subset_rfl hg hN

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

/-- The comparison function of the radial estimate: for `s < R` and `α ≠ 0`, the derivative of
`s ↦ (M / α) (A - (R - s)^α)` is `M (R - s)^(α - 1)`. -/
private theorem hasDerivAt_div_mul_sub_rpow {M α R s : ℝ} (A : ℝ) (hα : α ≠ 0) (hs : s < R) :
    HasDerivAt (fun s ↦ M / α * (A - (R - s) ^ α)) (M * (R - s) ^ (α - 1)) s := by
  have h := (((hasDerivAt_id' s).const_sub R).rpow_const (p := α) (Or.inl (by
    linarith))).const_sub A |>.const_mul (M / α)
  convert h using 1
  field_simp

/-- Along a ray from the centre of the ball `B_R(x₀)`, a function whose derivative is at most
`M (R - dist x x₀)^(α - 1)` moves by at most `(M / α) (R - ρ)^α` between the point at distance `ρ`
from the centre and the point `z`, since the bound integrates to `(M / α) (R - s)^α`. -/
private theorem norm_sub_le_of_norm_fderiv_le_mul_rpow_of_mem_ball {g : E → F} {x₀ z : E}
    {R ρ : ℝ} {M α : ℝ≥0} (hα : 0 < α) (hα1 : α ≤ 1) (hg : DifferentiableOn ℝ g (ball x₀ R))
    (hM : ∀ x ∈ ball x₀ R, ‖fderiv ℝ g x‖ ≤ M * (R - dist x x₀) ^ ((α : ℝ) - 1))
    (hz : z ∈ ball x₀ R) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ dist z x₀) :
    ‖g z - g (x₀ + (ρ / dist z x₀) • (z - x₀))‖ ≤ M / α * (R - ρ) ^ (α : ℝ) := by
  set d := dist z x₀
  have hdR : d < R := mem_ball.1 hz
  have hα0 : (α : ℝ) ≠ 0 := by exact_mod_cast hα.ne'
  -- The ray `γ s = x₀ + s • u` reaches `z` at `s = d` and stays within distance `s` of `x₀`.
  set u : E := d⁻¹ • (z - x₀)
  set γ : ℝ → E := fun s ↦ x₀ + s • u
  have hu : ‖u‖ ≤ 1 := by
    rw [norm_smul, norm_inv, Real.norm_of_nonneg dist_nonneg, ← dist_eq_norm]
    exact inv_mul_le_one
  have hγd : γ d = z := by
    rcases eq_or_ne d 0 with h | h
    · simp [γ, u, h, dist_eq_zero.1 h]
    · simp [γ, u, smul_smul, mul_inv_cancel₀ h]
  have hγρ : γ ρ = x₀ + (ρ / d) • (z - x₀) := by simp [γ, u, smul_smul, div_eq_mul_inv]
  have hγdist {s : ℝ} (hs : 0 ≤ s) : dist (γ s) x₀ ≤ s := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs]
    exact mul_le_of_le_one_right hs hu
  have hγball {s : ℝ} (hs : s ∈ Icc ρ d) (hs0 : 0 ≤ s) : γ s ∈ ball x₀ R :=
    mem_ball.2 ((hγdist hs0).trans_lt (hs.2.trans_lt hdR))
  have hderiv (s : ℝ) (hs : s ∈ Icc ρ d) :
      HasDerivAt (fun s ↦ g (γ s)) (fderiv ℝ g (γ s) u) s := by
    have hγ : HasDerivAt γ u s :=
      (((hasDerivAt_id s).smul_const u).const_add x₀).congr_deriv (one_smul ℝ u)
    exact ((hg.differentiableAt (isOpen_ball.mem_nhds (hγball hs (hρ0.trans hs.1)))).hasFDerivAt
      ).comp_hasDerivAt s hγ
  -- Compare `g ∘ γ - g (γ ρ)` with `B s = (M / α) ((R - ρ)^α - (R - s)^α)`.
  have hB (s : ℝ) (hs : s < R) := hasDerivAt_div_mul_sub_rpow (M := M) ((R - ρ) ^ (α : ℝ)) hα0 hs
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary'
    (f := fun s ↦ g (γ s) - g (γ ρ)) (a := ρ) (b := d)
    (f' := fun s ↦ fderiv ℝ g (γ s) u)
    (B := fun s ↦ M / α * ((R - ρ) ^ (α : ℝ) - (R - s) ^ (α : ℝ)))
    (B' := fun s ↦ M * (R - s) ^ ((α : ℝ) - 1))
    (fun s hs ↦ ((hderiv s hs).continuousAt.sub continuousAt_const).continuousWithinAt)
    (fun s hs ↦ ((hderiv s (Ico_subset_Icc_self hs)).sub_const _).hasDerivWithinAt)
    (by simp) (fun s hs ↦ (hB s (hs.2.trans_lt hdR)).continuousAt.continuousWithinAt)
    (fun s hs ↦ (hB s (hs.2.trans hdR)).hasDerivWithinAt) (fun s hs ↦ ?_)
    (right_mem_Icc.2 hρ)
  · rw [hγd, hγρ] at key
    exact key.trans (mul_le_mul_of_nonneg_left
      (sub_le_self _ (Real.rpow_nonneg (by linarith) _)) (by positivity))
  · have hs0 : 0 ≤ s := hρ0.trans hs.1
    have hsR : s < R := hs.2.trans hdR
    calc ‖fderiv ℝ g (γ s) u‖ ≤ ‖fderiv ℝ g (γ s)‖ * ‖u‖ := (fderiv ℝ g (γ s)).le_opNorm u
      _ ≤ ‖fderiv ℝ g (γ s)‖ := mul_le_of_le_one_right (norm_nonneg _) hu
      _ ≤ M * (R - dist (γ s) x₀) ^ ((α : ℝ) - 1) := hM _ (hγball (Ico_subset_Icc_self hs) hs0)
      _ ≤ M * (R - s) ^ ((α : ℝ) - 1) := by
        gcongr ?_ * ?_
        exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith [hγdist hs0])
          (by linarith [show (α : ℝ) ≤ 1 by exact_mod_cast hα1])

/-- Under the derivative bound `M (R - dist x x₀)^(α - 1)` on `B_R(x₀)`, every point `z` of the
ball has a point `z'` of the smaller closed ball `closedBall x₀ ρ`, for `0 ≤ ρ ≤ R`, within
distance `R - ρ` of `z` and with `‖g z - g z'‖ ≤ (M / α) (R - ρ)^α`: the point `z` itself if it
already lies there, and otherwise the point at distance `ρ` from `x₀` on the ray through `z`. -/
private theorem exists_mem_closedBall_norm_sub_le_of_norm_fderiv_le_mul_rpow {g : E → F}
    {x₀ z : E} {R ρ : ℝ} {M α : ℝ≥0} (hα : 0 < α) (hα1 : α ≤ 1)
    (hg : DifferentiableOn ℝ g (ball x₀ R))
    (hM : ∀ x ∈ ball x₀ R, ‖fderiv ℝ g x‖ ≤ M * (R - dist x x₀) ^ ((α : ℝ) - 1))
    (hz : z ∈ ball x₀ R) (hρ0 : 0 ≤ ρ) (hρR : ρ ≤ R) :
    ∃ z' ∈ closedBall x₀ ρ, dist z z' ≤ R - ρ ∧ ‖g z - g z'‖ ≤ M / α * (R - ρ) ^ (α : ℝ) := by
  have hdR : dist z x₀ < R := mem_ball.1 hz
  by_cases h : dist z x₀ ≤ ρ
  · exact ⟨z, mem_closedBall.2 h, by simpa using hρR, by
      simpa using mul_nonneg (by positivity : (0 : ℝ) ≤ M / α)
        (Real.rpow_nonneg (sub_nonneg.2 hρR) _)⟩
  push Not at h
  have hd0 : dist z x₀ ≠ 0 := (hρ0.trans_lt h).ne'
  refine ⟨x₀ + (ρ / dist z x₀) • (z - x₀), ?_, ?_,
    norm_sub_le_of_norm_fderiv_le_mul_rpow_of_mem_ball hα hα1 hg hM hz hρ0 h.le⟩
  · rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, ← dist_eq_norm,
      Real.norm_of_nonneg (div_nonneg hρ0 dist_nonneg), div_mul_cancel₀ _ hd0]
  · have : z - (x₀ + (ρ / dist z x₀) • (z - x₀)) = (1 - ρ / dist z x₀) • (z - x₀) := by
      rw [sub_smul, one_smul]; abel
    rw [dist_eq_norm, this, norm_smul, Real.norm_of_nonneg (by
      rw [sub_nonneg, div_le_one (hρ0.trans_lt h)]; exact h.le), ← dist_eq_norm, sub_mul,
      one_mul, div_mul_cancel₀ _ hd0]
    linarith

/-- Under the derivative bound `M (R - dist x x₀)^(α - 1)` on `B_R(x₀)`, with `α ≤ 1`, the
function is `M δ^(α - 1)`-Lipschitz on the closed ball of radius `R - δ`, for `δ > 0`. -/
private theorem norm_sub_le_of_mem_closedBall_of_norm_fderiv_le_mul_rpow {g : E → F}
    {x₀ w₁ w₂ : E} {R δ : ℝ} {M α : ℝ≥0} (hα1 : α ≤ 1) (hg : DifferentiableOn ℝ g (ball x₀ R))
    (hM : ∀ x ∈ ball x₀ R, ‖fderiv ℝ g x‖ ≤ M * (R - dist x x₀) ^ ((α : ℝ) - 1)) (hδ : 0 < δ)
    (hw₁ : w₁ ∈ closedBall x₀ (R - δ)) (hw₂ : w₂ ∈ closedBall x₀ (R - δ)) :
    ‖g w₂ - g w₁‖ ≤ M * δ ^ ((α : ℝ) - 1) * ‖w₂ - w₁‖ := by
  have hsub : closedBall x₀ (R - δ) ⊆ ball x₀ R := closedBall_subset_ball (by linarith)
  refine (convex_closedBall x₀ (R - δ)).norm_image_sub_le_of_norm_fderiv_le
    (fun w hw ↦ hg.differentiableAt (isOpen_ball.mem_nhds (hsub hw))) (fun w hw ↦ ?_) hw₁ hw₂
  refine (hM w (hsub hw)).trans (mul_le_mul_of_nonneg_left ?_ M.coe_nonneg)
  exact Real.rpow_le_rpow_of_nonpos hδ (by linarith [mem_closedBall.1 hw])
    (by linarith [show (α : ℝ) ≤ 1 by exact_mod_cast hα1])

/-- **The lemma of Hardy and Littlewood.** A function differentiable on the ball `B_R(x₀)` whose
derivative grows at most like `M (R - dist x x₀)^(α - 1)` towards the boundary, with
`0 < α ≤ 1`, is `α`-Hölder on `B_R(x₀)` with constant `(3 + 2 / α) M`. For instance, a
holomorphic function on the unit disc with `|f'(z)| ≤ M (1 - |z|)^(α - 1)` is `α`-Hölder there. -/
theorem holderOnWith_ball_of_norm_fderiv_le_mul_rpow {g : E → F} {x₀ : E} {R : ℝ}
    {M α : ℝ≥0} (hα : 0 < α) (hα1 : α ≤ 1) (hg : DifferentiableOn ℝ g (ball x₀ R))
    (hM : ∀ x ∈ ball x₀ R, ‖fderiv ℝ g x‖ ≤ M * (R - dist x x₀) ^ ((α : ℝ) - 1)) :
    HolderOnWith ((3 + 2 / α) * M) α g (ball x₀ R) := by
  refine HolderOnWith.of_dist_le fun z₁ hz₁ z₂ hz₂ ↦ ?_
  set δ := dist z₁ z₂
  have hR : 0 < R := pos_of_mem_ball hz₁
  have hMα : (0 : ℝ) ≤ M / α := by positivity
  have hC : (((3 + 2 / α) * M : ℝ≥0) : ℝ) = 3 * M + 2 * (M / α) := by push_cast; ring
  rw [hC, dist_eq_norm]
  rcases eq_or_lt_of_le (dist_nonneg : 0 ≤ δ) with hδ | hδ
  · obtain rfl : z₁ = z₂ := dist_eq_zero.1 hδ.symm
    rw [sub_self, norm_zero]
    positivity
  rcases le_or_gt R δ with hRδ | hδR
  · -- Far apart: compare both points with the centre `x₀`.
    obtain ⟨z₁', hz₁', -, h₁⟩ :=
      exists_mem_closedBall_norm_sub_le_of_norm_fderiv_le_mul_rpow hα hα1 hg hM hz₁ le_rfl hR.le
    obtain ⟨z₂', hz₂', -, h₂⟩ :=
      exists_mem_closedBall_norm_sub_le_of_norm_fderiv_le_mul_rpow hα hα1 hg hM hz₂ le_rfl hR.le
    rw [closedBall_zero, mem_singleton_iff] at hz₁' hz₂'
    rw [hz₁', sub_zero] at h₁
    rw [hz₂', sub_zero] at h₂
    have hpow : R ^ (α : ℝ) ≤ δ ^ (α : ℝ) := Real.rpow_le_rpow hR.le hRδ α.coe_nonneg
    calc ‖g z₁ - g z₂‖ ≤ ‖g z₁ - g x₀‖ + ‖g z₂ - g x₀‖ := by
          rw [norm_sub_rev (g z₂)]; exact norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ M / α * R ^ (α : ℝ) + M / α * R ^ (α : ℝ) := add_le_add h₁ h₂
      _ ≤ (3 * M + 2 * (M / α)) * δ ^ (α : ℝ) := by
        nlinarith [mul_le_mul_of_nonneg_left hpow hMα, Real.rpow_nonneg hδ.le (α : ℝ),
          M.coe_nonneg]
  · -- Nearby: move both points to the closed ball of radius `R - δ` and join them there.
    obtain ⟨z₁', hz₁', hd₁, h₁⟩ := exists_mem_closedBall_norm_sub_le_of_norm_fderiv_le_mul_rpow
      hα hα1 hg hM hz₁ (sub_nonneg.2 hδR.le) (sub_le_self _ hδ.le)
    obtain ⟨z₂', hz₂', hd₂, h₂⟩ := exists_mem_closedBall_norm_sub_le_of_norm_fderiv_le_mul_rpow
      hα hα1 hg hM hz₂ (sub_nonneg.2 hδR.le) (sub_le_self _ hδ.le)
    rw [sub_sub_cancel] at hd₁ hd₂ h₁ h₂
    have hmid := norm_sub_le_of_mem_closedBall_of_norm_fderiv_le_mul_rpow hα1 hg hM hδ hz₁' hz₂'
    have hd : ‖z₂' - z₁'‖ ≤ 3 * δ := by
      rw [← dist_eq_norm]
      linarith [dist_triangle4 z₂' z₂ z₁ z₁', dist_comm z₂' z₂, dist_comm z₂ z₁]
    have hpow : δ ^ ((α : ℝ) - 1) * δ = δ ^ (α : ℝ) := by
      rw [Real.rpow_sub_one hδ.ne', div_mul_cancel₀ _ hδ.ne']
    calc ‖g z₁ - g z₂‖ ≤ ‖g z₁ - g z₁'‖ + ‖g z₂' - g z₁'‖ + ‖g z₂ - g z₂'‖ := by
          rw [norm_sub_rev (g z₂') (g z₁'), norm_sub_rev (g z₂) (g z₂')]
          linarith [norm_sub_le_norm_sub_add_norm_sub (g z₁) (g z₁') (g z₂),
            norm_sub_le_norm_sub_add_norm_sub (g z₁') (g z₂') (g z₂)]
      _ ≤ M / α * δ ^ (α : ℝ) + M * δ ^ ((α : ℝ) - 1) * (3 * δ) + M / α * δ ^ (α : ℝ) := by
          gcongr
          exact hmid.trans (mul_le_mul_of_nonneg_left hd (by positivity))
      _ = (3 * M + 2 * (M / α)) * δ ^ (α : ℝ) := by rw [← hpow]; ring

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
