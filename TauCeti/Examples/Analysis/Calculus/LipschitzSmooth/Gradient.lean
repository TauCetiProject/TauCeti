/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.LipschitzSmooth.Gradient
public import TauCeti.Analysis.Calculus.LipschitzSmooth.Operations
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Linear

/-!
# Checks for smooth functions on a Hilbert space

Two families test the constants in the gradient inequalities of a `K`-smooth function.

* The quadratic `x ↦ K / 2 * ‖x‖ ^ 2` is `K`-smooth with gradient `K • x`. For it the quadratic
  upper bound, the sufficient decrease inequality and the gradient bound (with lower bound `0`)
  are all equalities, so none of their constants can be improved. The quadratic lower bound misses
  by exactly `K * ‖y - x‖ ^ 2`, the full width between the two bounds.
* An affine function `x ↦ c + ⟪a, x⟫` is `0`-smooth with gradient `a`, and both quadratic bounds
  are equalities. A `0`-smooth function that is bounded below has gradient `0` everywhere.
-/

public section

open scoped NNReal Gradient RealInnerProductSpace

namespace TauCeti.LipschitzSmoothExample

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

section Quadratic

variable (K : ℝ≥0)

omit [CompleteSpace E] in
/-- The multiple `K • id` of the identity is symmetric. -/
private theorem isSymmetric_smul_id :
    (((K : ℝ) • ContinuousLinearMap.id ℝ E : E →L[ℝ] E) : E →ₗ[ℝ] E).IsSymmetric := fun u v ↦ by
  simp [real_inner_smul_left, real_inner_smul_right]

omit [CompleteSpace E] in
/-- The quadratic `x ↦ K / 2 * ‖x‖ ^ 2` is the quadratic form of `K • id`. -/
private theorem half_mul_norm_sq_eq :
    (fun x : E ↦ (K : ℝ) / 2 * ‖x‖ ^ 2) =
      fun x ↦ ⟪((K : ℝ) • ContinuousLinearMap.id ℝ E) x, x⟫ / 2 := by
  funext x
  simp only [smul_apply, ContinuousLinearMap.id_apply, real_inner_smul_left,
    real_inner_self_eq_norm_sq]
  ring

omit [CompleteSpace E] in
/-- The quadratic `x ↦ K / 2 * ‖x‖ ^ 2` is `K`-smooth. -/
theorem lipschitzSmoothWith_half_mul_norm_sq :
    LipschitzSmoothWith ℝ K fun x : E ↦ (K : ℝ) / 2 * ‖x‖ ^ 2 := by
  rw [half_mul_norm_sq_eq]
  refine ((K : ℝ) • ContinuousLinearMap.id ℝ E).lipschitzSmoothWith_inner_div_two.weaken
    (NNReal.coe_le_coe.1 ?_)
  rw [coe_nnNorm]
  calc ‖(K : ℝ) • ContinuousLinearMap.id ℝ E‖
      ≤ ‖(K : ℝ)‖ * ‖ContinuousLinearMap.id ℝ E‖ := ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ K * 1 := by
        gcongr
        · exact (Real.norm_of_nonneg K.coe_nonneg).le
        · exact ContinuousLinearMap.norm_id_le
    _ = K := mul_one _

/-- The gradient of `x ↦ K / 2 * ‖x‖ ^ 2` at `x` is `K • x`. -/
theorem gradient_half_mul_norm_sq (x : E) :
    ∇ (fun x : E ↦ (K : ℝ) / 2 * ‖x‖ ^ 2) x = (K : ℝ) • x := by
  rw [half_mul_norm_sq_eq, (isSymmetric_smul_id K).gradient_inner_div_two]
  simp

/-- For `x ↦ K / 2 * ‖x‖ ^ 2` the quadratic upper bound is an equality. -/
theorem half_mul_norm_sq_eq_add_inner_gradient_add (x y : E) :
    (K : ℝ) / 2 * ‖y‖ ^ 2 = K / 2 * ‖x‖ ^ 2 +
      ⟪∇ (fun x : E ↦ (K : ℝ) / 2 * ‖x‖ ^ 2) x, y - x⟫ + K / 2 * ‖y - x‖ ^ 2 := by
  rw [gradient_half_mul_norm_sq, real_inner_smul_left, inner_sub_right, norm_sub_sq_real,
    real_inner_self_eq_norm_sq, real_inner_comm x y]
  ring

/-- For `x ↦ K / 2 * ‖x‖ ^ 2` the quadratic lower bound misses by exactly `K * ‖y - x‖ ^ 2`. -/
theorem half_mul_norm_sq_sub_add_inner_gradient_sub (x y : E) :
    (K : ℝ) / 2 * ‖y‖ ^ 2 - (K / 2 * ‖x‖ ^ 2 +
      ⟪∇ (fun x : E ↦ (K : ℝ) / 2 * ‖x‖ ^ 2) x, y - x⟫ - K / 2 * ‖y - x‖ ^ 2) =
      K * ‖y - x‖ ^ 2 := by
  rw [half_mul_norm_sq_eq_add_inner_gradient_add K x y]
  ring

/-- For `x ↦ K / 2 * ‖x‖ ^ 2`, which is bounded below by `0`, the gradient bound is an
equality. -/
theorem norm_gradient_half_mul_norm_sq_sq (x : E) :
    ‖∇ (fun x : E ↦ (K : ℝ) / 2 * ‖x‖ ^ 2) x‖ ^ 2 = 2 * K * ((K : ℝ) / 2 * ‖x‖ ^ 2 - 0) := by
  rw [gradient_half_mul_norm_sq, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

/-- For `x ↦ K / 2 * ‖x‖ ^ 2` the sufficient decrease inequality is an equality, for every step
size `η`. -/
theorem half_mul_norm_sq_sub_smul_gradient (x : E) (η : ℝ) :
    (K : ℝ) / 2 * ‖x - η • ∇ (fun x : E ↦ (K : ℝ) / 2 * ‖x‖ ^ 2) x‖ ^ 2 =
      K / 2 * ‖x‖ ^ 2 -
        η * (1 - K * η / 2) * ‖∇ (fun x : E ↦ (K : ℝ) / 2 * ‖x‖ ^ 2) x‖ ^ 2 := by
  have hstep : x - η • (K : ℝ) • x = (1 - η * K) • x := by
    rw [sub_smul, one_smul, mul_smul]
  rw [gradient_half_mul_norm_sq, hstep, norm_smul, norm_smul, mul_pow, mul_pow, Real.norm_eq_abs,
    Real.norm_eq_abs, sq_abs, sq_abs]
  ring

end Quadratic

section Affine

variable (c : ℝ) (a : E)

omit [CompleteSpace E] in
/-- An affine function `x ↦ c + ⟪a, x⟫` is `0`-smooth. -/
theorem lipschitzSmoothWith_const_add_inner :
    LipschitzSmoothWith ℝ 0 fun x : E ↦ c + ⟪a, x⟫ :=
  (innerSL ℝ a).lipschitzSmoothWith.const_add c

/-- The gradient of `x ↦ c + ⟪a, x⟫` is `a`. -/
theorem gradient_const_add_inner (x : E) : ∇ (fun x : E ↦ c + ⟪a, x⟫) x = a := by
  refine HasGradientAt.gradient ?_
  rw [hasGradientAt_iff_hasFDerivAt]
  exact ((innerSL ℝ a).hasFDerivAt (x := x)).const_add c

/-- For an affine function the two quadratic bounds with `K = 0` coincide and are equalities. -/
theorem const_add_inner_eq_add_inner_gradient (x y : E) :
    c + ⟪a, y⟫ = c + ⟪a, x⟫ + ⟪∇ (fun x : E ↦ c + ⟪a, x⟫) x, y - x⟫ +
      ((0 : ℝ≥0) : ℝ) / 2 * ‖y - x‖ ^ 2 := by
  rw [gradient_const_add_inner, inner_sub_right]
  simp

/-- A `0`-smooth function that is bounded below has gradient `0` everywhere. -/
theorem gradient_eq_zero_of_lipschitzSmoothWith_zero {f : E → ℝ} {m : ℝ}
    (hf : LipschitzSmoothWith ℝ 0 f) (hm : ∀ y, m ≤ f y) (x : E) : ∇ f x = 0 := by
  simpa using hf.norm_gradient_sq_le hm x

end Affine

end TauCeti.LipschitzSmoothExample
