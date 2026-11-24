/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.LipschitzSmooth.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Smooth functions on a Hilbert space: gradient inequalities

Let `f` be a `K`-smooth real function on a real Hilbert space `E`, in the sense of
`LipschitzSmoothWith ℝ K f`. This file states the two quadratic bounds with the gradient,

`f x + ⟪∇ f x, y - x⟫ - K / 2 * ‖y - x‖ ^ 2 ≤ f y ≤ f x + ⟪∇ f x, y - x⟫ + K / 2 * ‖y - x‖ ^ 2`,

and derives the two estimates on which the analysis of gradient descent rests. A gradient step of
any size `η` satisfies `f (x - η • ∇ f x) ≤ f x - η * (1 - K * η / 2) * ‖∇ f x‖ ^ 2`. So when
`0 < η` and `K * η < 2` the step does not increase `f`, and it strictly decreases `f` if
`∇ f x ≠ 0`. If `f` is bounded below by `m`, then `‖∇ f x‖ ^ 2 ≤ 2 * K * (f x - m)`.

The model example is a quadratic form. For every continuous linear map `A` on a real inner product
space the function `x ↦ ⟪A x, x⟫ / 2` is `‖A‖₊`-smooth, with no symmetry assumption, and the
quadratic `y ↦ a / 2 * ‖y‖ ^ 2 + c` is `‖a‖₊`-smooth.

## Main results

* `LipschitzSmoothWith.le_add_inner_gradient_add`,
  `LipschitzSmoothWith.add_inner_gradient_sub_le`: the quadratic upper and lower bounds.
* `LipschitzSmoothWith.apply_sub_smul_gradient_le`: sufficient decrease along the gradient.
* `LipschitzSmoothWith.norm_gradient_sq_le`: the gradient bound for a function bounded below.
* `ContinuousLinearMap.lipschitzSmoothWith_inner_div_two`,
  `TauCeti.lipschitzSmoothWith_mul_norm_sq_add`: quadratic forms.

## References

* Y. Nesterov, *Lectures on convex optimization*, 2nd ed., Springer, 2018, Lemma 1.2.3 and
  (1.2.19).
-/

public section

open scoped NNReal Gradient RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace LipschitzSmoothWith

variable {K : ℝ≥0} {f : E → ℝ}

/-- The quadratic upper bound of a `K`-smooth function, with the gradient. -/
theorem le_add_inner_gradient_add (hf : LipschitzSmoothWith ℝ K f) (x y : E) :
    f y ≤ f x + ⟪∇ f x, y - x⟫ + K / 2 * ‖y - x‖ ^ 2 := by
  simpa only [inner_gradient_left, dist_eq_norm'] using hf.fderiv_descent_le x y

/-- The quadratic lower bound of a `K`-smooth function, with the gradient. -/
theorem add_inner_gradient_sub_le (hf : LipschitzSmoothWith ℝ K f) (x y : E) :
    f x + ⟪∇ f x, y - x⟫ - K / 2 * ‖y - x‖ ^ 2 ≤ f y := by
  simpa only [inner_gradient_left, dist_eq_norm'] using hf.fderiv_descent_ge x y

/-- **Sufficient decrease.** A gradient step of size `η` from `x` changes a `K`-smooth function
by at most `-η * (1 - K * η / 2) * ‖∇ f x‖ ^ 2`, for every real `η`. -/
theorem apply_sub_smul_gradient_le (hf : LipschitzSmoothWith ℝ K f) (x : E) (η : ℝ) :
    f (x - η • ∇ f x) ≤ f x - η * (1 - K * η / 2) * ‖∇ f x‖ ^ 2 := by
  have h := hf.le_add_inner_gradient_add x (x - η • ∇ f x)
  simp only [sub_sub_cancel_left, inner_neg_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, norm_neg, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at h
  linarith

/-- **The gradient bound at a lower bound.** If a `K`-smooth function is bounded below by `m`,
then `‖∇ f x‖ ^ 2 ≤ 2 * K * (f x - m)`. -/
theorem norm_gradient_sq_le {m : ℝ} (hf : LipschitzSmoothWith ℝ K f) (hm : ∀ y, m ≤ f y)
    (x : E) : ‖∇ f x‖ ^ 2 ≤ 2 * K * (f x - m) := by
  -- Every step size gives `η * (1 - K * η / 2) * ‖∇ f x‖ ^ 2 ≤ f x - m`.
  have key (η : ℝ) : η * (1 - K * η / 2) * ‖∇ f x‖ ^ 2 ≤ f x - m := by
    linarith [hf.apply_sub_smul_gradient_le x η, hm (x - η • ∇ f x)]
  rcases eq_or_ne K 0 with rfl | hK
  · -- For `K = 0` the bound holds for every `η`, which forces the gradient to vanish.
    by_contra! h
    simp only [NNReal.coe_zero, mul_zero, zero_mul] at h
    have := key ((f x - m + 1) / ‖∇ f x‖ ^ 2)
    simp only [NNReal.coe_zero, zero_mul, zero_div, sub_zero, mul_one,
      div_mul_cancel₀ _ h.ne'] at this
    linarith
  · have hK' : (0 : ℝ) < K := by positivity
    have := key (1 / K)
    rw [mul_one_div_cancel hK'.ne'] at this
    calc ‖∇ f x‖ ^ 2 = 2 * K * (1 / K * (1 - 1 / 2) * ‖∇ f x‖ ^ 2) := by
          field_simp
          ring
      _ ≤ 2 * K * (f x - m) := by gcongr

end LipschitzSmoothWith

section Quadratic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The quadratic form `x ↦ ⟪A x, x⟫ / 2` of a continuous linear map `A` is `‖A‖₊`-smooth. No
symmetry is needed: the first-order Taylor remainder at `x` is `⟪A (y - x), y - x⟫ / 2`. -/
theorem ContinuousLinearMap.lipschitzSmoothWith_inner_div_two (A : E →L[ℝ] E) :
    LipschitzSmoothWith ℝ ‖A‖₊ fun x ↦ ⟪A x, x⟫ / 2 := by
  have hd (x : E) : HasFDerivAt (fun x ↦ ⟪A x, x⟫ / 2)
      ((2⁻¹ : ℝ) • fderivInnerCLM ℝ (A x, x) ∘L A.prod (ContinuousLinearMap.id ℝ E)) x := by
    simpa [div_eq_mul_inv] using
      ((A.hasFDerivAt (x := x)).inner ℝ (hasFDerivAt_id x)).mul_const (2⁻¹ : ℝ)
  refine .of_hasFDerivAt hd fun x y ↦ ?_
  have key : ⟪A y, y⟫ / 2 - ⟪A x, x⟫ / 2 -
      ((2⁻¹ : ℝ) • fderivInnerCLM ℝ (A x, x) ∘L A.prod (ContinuousLinearMap.id ℝ E)) (y - x) =
      ⟪A (y - x), y - x⟫ / 2 := by
    simp only [smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply, fderivInnerCLM_apply, map_sub, inner_sub_left,
      inner_sub_right, smul_eq_mul]
    ring
  rw [key]
  simp only [norm_div, Real.norm_eq_abs, Nat.abs_ofNat, coe_nnNorm, dist_eq_norm']
  calc |⟪A (y - x), y - x⟫| / 2 ≤ ‖A‖ * ‖y - x‖ * ‖y - x‖ / 2 := by
        gcongr
        exact (abs_real_inner_le_norm _ _).trans (by gcongr; exact A.le_opNorm _)
    _ = ‖A‖ / 2 * ‖y - x‖ ^ 2 := by ring

/-- Over `ℝ`, the quadratic `y ↦ a / 2 * ‖y‖ ^ 2 + c` is `‖a‖₊`-smooth. -/
theorem TauCeti.lipschitzSmoothWith_mul_norm_sq_add (a c : ℝ) :
    LipschitzSmoothWith ℝ ‖a‖₊ fun y : E ↦ a / 2 * ‖y‖ ^ 2 + c := by
  have hfun : (fun y : E ↦ a / 2 * ‖y‖ ^ 2 + c) =
      fun y ↦ ⟪(a • ContinuousLinearMap.id ℝ E) y, y⟫ / 2 + c := by
    funext y
    simp only [smul_apply, ContinuousLinearMap.id_apply, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
    ring
  rw [hfun]
  refine ((a • ContinuousLinearMap.id ℝ E).lipschitzSmoothWith_inner_div_two.weaken
    (NNReal.coe_le_coe.1 ?_)).add_const c
  simp only [coe_nnNorm]
  calc ‖a • ContinuousLinearMap.id ℝ E‖
      ≤ ‖a‖ * ‖ContinuousLinearMap.id ℝ E‖ := ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ ‖a‖ * 1 := by
        gcongr
        exact ContinuousLinearMap.norm_id_le
    _ = ‖a‖ := mul_one _

end Quadratic
