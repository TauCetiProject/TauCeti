/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# First-order conditions for penalized least squares

Let `A : E →ₗ[ℝ] F` be a linear map from a real vector space to a real inner product space,
`y : F`, `c : ℝ` and `h : E → ℝ`. This file studies the minimizers of the penalized
least-squares objective

`f(z) = c ‖y - A z‖² / 2 + h(z)`,

which covers the lasso (`h` a multiple of the `ℓ¹` norm) and nuclear-norm penalized trace
regression. For `c ≥ 0` and a convex penalty `h`, a point `x` minimizes `f` iff `c A*(y - A x)`
is a subgradient of `h` at `x`, written without adjoints as the variational inequality
`c ⟪y - A x, A (b - x)⟫ ≤ h b - h x` for every `b`. For `c > 0` the strict convexity of the
quadratic part forces all minimizers to have the same image under `A`, and then the same
penalty; for `c = 0` the minimizers of `h` trivially have the same penalty.

## Main results

* `IsMinOn.mul_inner_le`: the variational inequality at a minimizer, for a convex `h`;
  `IsMinOn.mul_inner_le_of_forall_mem_Ioo` is the same inequality for a single `b`, assuming only
  that `h` lies below its chord from `x` to `b`.
* `TauCeti.isMinOn_of_forall_mul_inner_le`: the converse, for `c ≥ 0` and any `h`;
  `TauCeti.isMinOn_iff_forall_mul_inner_le` combines the two.
* `IsMinOn.mul_norm_sq_le`: the sharper form `c ‖A (x - b)‖² ≤ c ⟪y - A b, A (x - b)⟫ + h b - h x`.
* `IsMinOn.map_eq_of_isMinOn`, `IsMinOn.apply_eq_of_isMinOn`: for a convex `h`, any two
  minimizers have the same image under `A` if `c > 0`, and the same penalty if `c ≥ 0`.
-/

public section

open Set Filter Topology
open scoped RealInnerProductSpace

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] {A : E →ₗ[ℝ] F} {y : F} {c : ℝ} {h : E → ℝ} {x x' : E}

/-- The change of the penalized least-squares objective between `x` and `b`. -/
private theorem penalized_sub_eq (A : E →ₗ[ℝ] F) (y : F) (c : ℝ) (h : E → ℝ) (x b : E) :
    c * ‖y - A b‖ ^ 2 / 2 + h b - (c * ‖y - A x‖ ^ 2 / 2 + h x) =
      c * ‖A (b - x)‖ ^ 2 / 2 - c * ⟪y - A x, A (b - x)⟫ + (h b - h x) := by
  have hy : y - A b = (y - A x) - A (b - x) := by rw [map_sub]; abel
  rw [hy, norm_sub_sq_real]
  ring

namespace IsMinOn

/-- At a minimizer `x` of `c ‖y - A z‖² / 2 + h z`, the variational inequality
`c ⟪y - A x, A (b - x)⟫ ≤ h b - h x` holds for every `b` such that `h` lies below its chord
from `x` to `b`. -/
theorem mul_inner_le_of_forall_mem_Ioo
    (hx : IsMinOn (fun z ↦ c * ‖y - A z‖ ^ 2 / 2 + h z) univ x) {b : E}
    (hb : ∀ s ∈ Ioo (0 : ℝ) 1, h (x + s • (b - x)) ≤ h x + s * (h b - h x)) :
    c * ⟪y - A x, A (b - x)⟫ ≤ h b - h x := by
  -- Along the segment, `0 ≤ f (x + s (b - x)) - f x ≤ s D + s² Q`; divide by `s` and let `s → 0`.
  set D := h b - h x - c * ⟪y - A x, A (b - x)⟫
  set Q := c * ‖A (b - x)‖ ^ 2 / 2
  have key : ∀ s ∈ Ioo (0 : ℝ) 1, 0 ≤ D + s * Q := by
    intro s hs
    have h1 := penalized_sub_eq A y c h x (x + s • (b - x))
    have h2 := isMinOn_univ_iff.1 hx (x + s • (b - x))
    simp only [add_sub_cancel_left, map_smul, norm_smul, inner_smul_right, Real.norm_eq_abs,
      mul_pow, sq_abs] at h1
    have h3 := hb s hs
    have h4 : 0 ≤ s * (D + s * Q) := by
      simp only [D, Q] at h2 ⊢
      nlinarith
    exact (mul_nonneg_iff_of_pos_left hs.1).1 h4
  have hlim : Tendsto (fun s : ℝ ↦ D + s * Q) (𝓝[>] 0) (𝓝 D) := by
    have h0 : Tendsto (fun s : ℝ ↦ s) (𝓝[>] 0) (𝓝 0) := tendsto_nhdsWithin_of_tendsto_nhds
      (continuous_id.tendsto 0)
    simpa using tendsto_const_nhds.add (h0.mul_const Q)
  have hD : 0 ≤ D := ge_of_tendsto hlim (eventually_of_mem (Ioo_mem_nhdsGT one_pos) key)
  linarith

/-- At a minimizer `x` of `c ‖y - A z‖² / 2 + h z` with `h` convex, the variational inequality
`c ⟪y - A x, A (b - x)⟫ ≤ h b - h x` holds for every `b`: `c A*(y - A x)` is a subgradient
of `h` at `x`. -/
theorem mul_inner_le (hx : IsMinOn (fun z ↦ c * ‖y - A z‖ ^ 2 / 2 + h z) univ x)
    (hh : ConvexOn ℝ univ h) (b : E) : c * ⟪y - A x, A (b - x)⟫ ≤ h b - h x :=
  hx.mul_inner_le_of_forall_mem_Ioo fun s hs ↦ by
    have hc := hh.2 (mem_univ x) (mem_univ b) (sub_nonneg.2 hs.2.le) hs.1.le (sub_add_cancel 1 s)
    have he : (1 - s) • x + s • b = x + s • (b - x) := by module
    rw [he, smul_eq_mul, smul_eq_mul] at hc
    linarith

/-- At a minimizer `x` of `c ‖y - A z‖² / 2 + h z` with `h` convex, for every `b`,
`c ‖A (x - b)‖² ≤ c ⟪y - A b, A (x - b)⟫ + (h b - h x)`. -/
theorem mul_norm_sq_le (hx : IsMinOn (fun z ↦ c * ‖y - A z‖ ^ 2 / 2 + h z) univ x)
    (hh : ConvexOn ℝ univ h) (b : E) :
    c * ‖A (x - b)‖ ^ 2 ≤ c * ⟪y - A b, A (x - b)⟫ + (h b - h x) := by
  have h1 := hx.mul_inner_le hh b
  have hy : y - A b = (y - A x) + A (x - b) := by rw [map_sub]; abel
  have hbx : A (b - x) = -A (x - b) := by rw [← map_neg, neg_sub]
  rw [hbx, inner_neg_right] at h1
  rw [hy, inner_add_left, real_inner_self_eq_norm_sq]
  linarith

/-- For `c > 0` and a convex `h`, any two minimizers of `c ‖y - A z‖² / 2 + h z` have the same
image under `A`. -/
theorem map_eq_of_isMinOn (hc : 0 < c) (hh : ConvexOn ℝ univ h)
    (hx : IsMinOn (fun z ↦ c * ‖y - A z‖ ^ 2 / 2 + h z) univ x)
    (hx' : IsMinOn (fun z ↦ c * ‖y - A z‖ ^ 2 / 2 + h z) univ x') : A x = A x' := by
  have h1 := hx.mul_norm_sq_le hh x'
  have h2 := hx'.mul_inner_le hh x
  have h3 : ‖A (x - x')‖ ^ 2 ≤ 0 := le_of_mul_le_mul_left (by linarith) hc
  have h4 := (pow_eq_zero_iff two_ne_zero).1 (le_antisymm h3 (sq_nonneg _))
  rwa [norm_eq_zero, map_sub, sub_eq_zero] at h4

/-- For `c ≥ 0` and a convex `h`, any two minimizers of `c ‖y - A z‖² / 2 + h z` have the same
penalty. -/
theorem apply_eq_of_isMinOn (hc : 0 ≤ c) (hh : ConvexOn ℝ univ h)
    (hx : IsMinOn (fun z ↦ c * ‖y - A z‖ ^ 2 / 2 + h z) univ x)
    (hx' : IsMinOn (fun z ↦ c * ‖y - A z‖ ^ 2 / 2 + h z) univ x') : h x = h x' := by
  have h1 := isMinOn_univ_iff.1 hx x'
  have h2 := isMinOn_univ_iff.1 hx' x
  rcases hc.eq_or_lt with rfl | hc
  · simp only [zero_mul, zero_div, zero_add] at h1 h2
    exact le_antisymm h1 h2
  rw [hx.map_eq_of_isMinOn hc hh hx'] at h1 h2
  linarith

end IsMinOn

namespace TauCeti

/-- For `c ≥ 0`, a point `x` satisfying the variational inequality
`c ⟪y - A x, A (b - x)⟫ ≤ h b - h x` for every `b` minimizes `c ‖y - A z‖² / 2 + h z`. -/
theorem isMinOn_of_forall_mul_inner_le (hc : 0 ≤ c)
    (H : ∀ b, c * ⟪y - A x, A (b - x)⟫ ≤ h b - h x) :
    IsMinOn (fun z ↦ c * ‖y - A z‖ ^ 2 / 2 + h z) univ x := by
  refine isMinOn_univ_iff.2 fun b ↦ ?_
  have h1 := penalized_sub_eq A y c h x b
  have h2 : 0 ≤ c * ‖A (b - x)‖ ^ 2 / 2 := by positivity
  linarith [H b]

/-- For `c ≥ 0` and a convex `h`, a point `x` minimizes `c ‖y - A z‖² / 2 + h z` iff
`c ⟪y - A x, A (b - x)⟫ ≤ h b - h x` for every `b`. -/
theorem isMinOn_iff_forall_mul_inner_le (hc : 0 ≤ c) (hh : ConvexOn ℝ univ h) :
    IsMinOn (fun z ↦ c * ‖y - A z‖ ^ 2 / 2 + h z) univ x ↔
      ∀ b, c * ⟪y - A x, A (b - x)⟫ ≤ h b - h x :=
  ⟨fun hx ↦ hx.mul_inner_le hh, isMinOn_of_forall_mul_inner_le hc⟩

end TauCeti
