/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Gradient
public import TauCeti.Analysis.Calculus.LipschitzSmooth.Gradient

/-!
# Checks for smooth functions on a Hilbert space

Two families test the constants in the gradient inequalities of a `K`-smooth function.

* The quadratic `y ↦ K / 2 * ‖y‖ ^ 2 + c` is `K`-smooth with gradient `K • y` and is bounded below
  by `c`. For it the quadratic upper bound, the sufficient decrease inequality and the gradient
  bound are all equalities, so none of their constants can be improved. The quadratic lower bound
  misses by exactly `K * ‖y - x‖ ^ 2`, the full width between the two bounds.
* An affine function `x ↦ c + ⟪a, x⟫` is `0`-smooth with gradient `a`, and both quadratic bounds
  are equalities. A `0`-smooth function that is bounded below has gradient `0` everywhere.
-/

public section

open scoped NNReal Gradient RealInnerProductSpace

namespace TauCeti.LipschitzSmoothExample

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

section Quadratic

variable (K : ℝ≥0) (c : ℝ)

omit [CompleteSpace E] in
/-- The quadratic `y ↦ K / 2 * ‖y‖ ^ 2 + c` is `K`-smooth. -/
theorem lipschitzSmoothWith_coe_mul_norm_sq_add :
    LipschitzSmoothWith ℝ K fun y : E ↦ (K : ℝ) / 2 * ‖y‖ ^ 2 + c := by
  simpa using lipschitzSmoothWith_mul_norm_sq_add (E := E) (K : ℝ) c

/-- For `y ↦ K / 2 * ‖y‖ ^ 2 + c` the quadratic upper bound is an equality. -/
theorem mul_norm_sq_add_eq_add_inner_gradient_add (x y : E) :
    (K : ℝ) / 2 * ‖y‖ ^ 2 + c = K / 2 * ‖x‖ ^ 2 + c +
      ⟪∇ (fun y : E ↦ (K : ℝ) / 2 * ‖y‖ ^ 2 + c) x, y - x⟫ + K / 2 * ‖y - x‖ ^ 2 := by
  rw [gradient_mul_norm_sq_add]
  simp only [real_inner_smul_left, inner_sub_right, norm_sub_sq_real, real_inner_self_eq_norm_sq,
    real_inner_comm x y]
  ring

/-- For `y ↦ K / 2 * ‖y‖ ^ 2 + c` the quadratic lower bound misses by exactly
`K * ‖y - x‖ ^ 2`. -/
theorem mul_norm_sq_add_sub_add_inner_gradient_sub (x y : E) :
    (K : ℝ) / 2 * ‖y‖ ^ 2 + c - (K / 2 * ‖x‖ ^ 2 + c +
      ⟪∇ (fun y : E ↦ (K : ℝ) / 2 * ‖y‖ ^ 2 + c) x, y - x⟫ - K / 2 * ‖y - x‖ ^ 2) =
      K * ‖y - x‖ ^ 2 := by
  rw [mul_norm_sq_add_eq_add_inner_gradient_add K c x y]
  ring

/-- For `y ↦ K / 2 * ‖y‖ ^ 2 + c`, which is bounded below by `c`, the gradient bound is an
equality. -/
theorem norm_gradient_mul_norm_sq_add_sq (x : E) :
    ‖∇ (fun y : E ↦ (K : ℝ) / 2 * ‖y‖ ^ 2 + c) x‖ ^ 2 =
      2 * K * ((K : ℝ) / 2 * ‖x‖ ^ 2 + c - c) := by
  rw [gradient_mul_norm_sq_add]
  simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

/-- For `y ↦ K / 2 * ‖y‖ ^ 2 + c` the sufficient decrease inequality is an equality, for every
step size `η`. -/
theorem mul_norm_sq_add_sub_smul_gradient (x : E) (η : ℝ) :
    (K : ℝ) / 2 * ‖x - η • ∇ (fun y : E ↦ (K : ℝ) / 2 * ‖y‖ ^ 2 + c) x‖ ^ 2 + c =
      K / 2 * ‖x‖ ^ 2 + c -
        η * (1 - K * η / 2) * ‖∇ (fun y : E ↦ (K : ℝ) / 2 * ‖y‖ ^ 2 + c) x‖ ^ 2 := by
  have hstep : x - η • (K : ℝ) • x = (1 - η * K) • x := by module
  rw [gradient_mul_norm_sq_add, hstep]
  simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

end Quadratic

section Affine

variable (c : ℝ) (a : E)

omit [CompleteSpace E] in
/-- An affine function `x ↦ c + ⟪a, x⟫` is `0`-smooth. -/
theorem lipschitzSmoothWith_const_add_inner :
    LipschitzSmoothWith ℝ 0 fun x : E ↦ c + ⟪a, x⟫ :=
  (innerSL ℝ a).lipschitzSmoothWith.const_add c

/-- For an affine function the two quadratic bounds with `K = 0` coincide and are equalities. -/
theorem const_add_inner_eq_add_inner_gradient (x y : E) :
    c + ⟪a, y⟫ = c + ⟪a, x⟫ + ⟪∇ (fun x : E ↦ c + ⟪a, x⟫) x, y - x⟫ +
      ((0 : ℝ≥0) : ℝ) / 2 * ‖y - x‖ ^ 2 := by
  simp [inner_sub_right]

/-- A `0`-smooth function that is bounded below has gradient `0` everywhere. -/
theorem gradient_eq_zero_of_lipschitzSmoothWith_zero {f : E → ℝ} {m : ℝ}
    (hf : LipschitzSmoothWith ℝ 0 f) (hm : ∀ y, m ≤ f y) (x : E) : ∇ f x = 0 := by
  simpa using hf.norm_gradient_sq_le hm x

end Affine

end TauCeti.LipschitzSmoothExample
