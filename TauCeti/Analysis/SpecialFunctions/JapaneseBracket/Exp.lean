/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Analysis.SpecialFunctions.Sqrt

/-!
# Smooth radial exponential weights

For `b > 0`, the weight `exp(c √(b + ‖z‖²))` is smooth on any real inner product space. The
norm of its derivative is `|c| ‖z‖ / √(b + ‖z‖²)` times the weight, so it is bounded by `|c|`
times the weight, and by an arbitrarily small multiple of the weight on a fixed ball once `b` is
large. The usual choice is `b = 1`, and changing `b` changes the weight by at most a constant
factor.
-/

public section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {b : ℝ}

/-- The regularized radial exponential weight is smooth, of every order. -/
theorem contDiff_exp_mul_sqrt_add_norm_sq (c : ℝ) (hb : 0 < b) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun z : E ↦ Real.exp (c * √(b + ‖z‖ ^ 2))) := by
  have hq : ContDiff ℝ n (fun z : E ↦ b + ‖z‖ ^ 2) :=
    contDiff_const.add (contDiff_id.norm_sq ℝ)
  exact (contDiff_const.mul (hq.sqrt (fun z ↦ by positivity))).exp

/-- The derivative of the regularized radial exponential weight, as a real functional. -/
theorem fderiv_exp_mul_sqrt_add_norm_sq (c : ℝ) (hb : 0 < b) (z : E) :
    fderiv ℝ (fun t : E ↦ Real.exp (c * √(b + ‖t‖ ^ 2))) z =
      (Real.exp (c * √(b + ‖z‖ ^ 2)) * c / √(b + ‖z‖ ^ 2)) • innerSL ℝ z := by
  have hp : 0 < b + ‖z‖ ^ 2 := by positivity
  have hd :=
    ((((hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_add b).sqrt hp.ne').const_mul c).exp
  rw [hd.fderiv]
  ext v
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply]
  field_simp
  ring

/-- The exact norm of the derivative of the regularized radial exponential weight: the
logarithmic gradient has norm `|c| ‖z‖ / √(b + ‖z‖²)`. -/
theorem norm_fderiv_exp_mul_sqrt_add_norm_sq (c : ℝ) (hb : 0 < b) (z : E) :
    ‖fderiv ℝ (fun t : E ↦ Real.exp (c * √(b + ‖t‖ ^ 2))) z‖ =
      |c| * Real.exp (c * √(b + ‖z‖ ^ 2)) * (‖z‖ / √(b + ‖z‖ ^ 2)) := by
  rw [fderiv_exp_mul_sqrt_add_norm_sq c hb, norm_smul, innerSL_apply_norm, Real.norm_eq_abs,
    abs_div, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_nonneg (Real.sqrt_nonneg _)]
  ring

/-- The logarithmic gradient of the regularized radial exponential weight has norm
at most `|c|`, with no restriction on the sign of `c`. -/
theorem norm_fderiv_exp_mul_sqrt_add_norm_sq_le (c : ℝ) (hb : 0 < b) (z : E) :
    ‖fderiv ℝ (fun t : E ↦ Real.exp (c * √(b + ‖t‖ ^ 2))) z‖ ≤
      |c| * Real.exp (c * √(b + ‖z‖ ^ 2)) := by
  have hp : 0 < b + ‖z‖ ^ 2 := by positivity
  have hq : ‖z‖ / √(b + ‖z‖ ^ 2) ≤ 1 := by
    apply (div_le_one (Real.sqrt_pos.2 hp)).2
    exact (Real.le_sqrt (norm_nonneg z) hp.le).2 (by linarith)
  rw [norm_fderiv_exp_mul_sqrt_add_norm_sq c hb]
  exact mul_le_of_le_one_right (by positivity) hq

omit [InnerProductSpace ℝ E] in
/-- Changing the regularization parameter changes the radial exponential weight by at most the
factor `exp(|c| √|s - t|)`, uniformly in `z`, since the square root is `1/2`-Hölder. -/
theorem exp_mul_sqrt_add_norm_sq_le (c s t : ℝ) (z : E) :
    Real.exp (c * √(s + ‖z‖ ^ 2)) ≤
      Real.exp (|c| * √|s - t|) * Real.exp (c * √(t + ‖z‖ ^ 2)) := by
  rw [← Real.exp_add, Real.exp_le_exp]
  have hd := Real.abs_sqrt_sub_sqrt_le (s + ‖z‖ ^ 2) (t + ‖z‖ ^ 2)
  rw [add_sub_add_right_eq_sub] at hd
  have h := (abs_le.mp ((abs_mul c _).symm ▸
    mul_le_mul_of_nonneg_left hd (abs_nonneg c))).2
  linarith [mul_sub c (√(s + ‖z‖ ^ 2)) (√(t + ‖z‖ ^ 2))]

end TauCeti
