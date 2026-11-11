/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Smooth radial exponential weights

The weight `exp(c √(1 + ‖z‖²))` is smooth on any real inner product space, and the
norm of its derivative is bounded by `|c|` times the weight.
-/

public section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The regularized radial exponential weight is smooth, of every order. -/
theorem contDiff_exp_mul_sqrt_one_add_norm_sq (c : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun z : E ↦ Real.exp (c * √(1 + ‖z‖ ^ 2))) := by
  have hq : ContDiff ℝ n (fun z : E ↦ 1 + ‖z‖ ^ 2) :=
    contDiff_const.add (contDiff_id.norm_sq ℝ)
  exact (contDiff_const.mul (hq.sqrt (fun z ↦ by positivity))).exp

/-- The derivative of the regularized radial exponential weight, as a real functional. -/
theorem fderiv_exp_mul_sqrt_one_add_norm_sq (c : ℝ) (z : E) :
    fderiv ℝ (fun t : E ↦ Real.exp (c * √(1 + ‖t‖ ^ 2))) z =
      (Real.exp (c * √(1 + ‖z‖ ^ 2)) * c / √(1 + ‖z‖ ^ 2)) • innerSL ℝ z := by
  have hp : 0 < 1 + ‖z‖ ^ 2 := by positivity
  have hd :=
    ((((hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_add 1).sqrt hp.ne').const_mul c).exp
  rw [hd.fderiv]
  ext v
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply]
  field_simp
  ring

/-- The logarithmic gradient of the regularized radial exponential weight has norm
at most `|c|`, with no restriction on the sign of `c`. -/
theorem norm_fderiv_exp_mul_sqrt_one_add_norm_sq_le (c : ℝ) (z : E) :
    ‖fderiv ℝ (fun t : E ↦ Real.exp (c * √(1 + ‖t‖ ^ 2))) z‖ ≤
      |c| * Real.exp (c * √(1 + ‖z‖ ^ 2)) := by
  have hp : 0 < 1 + ‖z‖ ^ 2 := by positivity
  have hb : ‖z‖ / √(1 + ‖z‖ ^ 2) ≤ 1 := by
    apply (div_le_one (Real.sqrt_pos.2 hp)).2
    exact (Real.le_sqrt (norm_nonneg z) hp.le).2 (by linarith)
  rw [fderiv_exp_mul_sqrt_one_add_norm_sq]
  calc
    _ = (|c| * Real.exp (c * √(1 + ‖z‖ ^ 2))) * (‖z‖ / √(1 + ‖z‖ ^ 2)) := by
      simp [norm_smul, abs_of_nonneg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    _ ≤ _ := mul_le_of_le_one_right (by positivity) hb

end TauCeti
