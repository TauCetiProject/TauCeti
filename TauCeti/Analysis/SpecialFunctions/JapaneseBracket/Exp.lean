/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import TauCeti.Analysis.SpecialFunctions.Sqrt

/-!
# Smooth radial exponential weights

For `b > 0`, the weight `exp(c √(b + ‖z‖²))` is smooth on any real inner product space. The
norm of its derivative is `|c| ‖z‖ / √(b + ‖z‖²)` times the weight, so it is bounded by `|c|`
times the weight, and by an arbitrarily small multiple of the weight on a fixed ball once `b` is
large. The usual choice is `b = 1`, and changing `b` changes the weight by at most a constant
factor. The truncated weights `W / (1 + ε W)`, `ε > 0`, are smooth, lie between `0` and
`min W (1 / ε)`, and have logarithmic gradient at most that of `W`.
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

omit [InnerProductSpace ℝ E] in
/-- The factor `‖z‖ / √(b + ‖z‖²)` in the logarithmic gradient is at most `1`. -/
theorem norm_div_sqrt_add_norm_sq_le_one (hb : 0 ≤ b) (z : E) : ‖z‖ / √(b + ‖z‖ ^ 2) ≤ 1 :=
  div_le_one_of_le₀ ((Real.le_sqrt (norm_nonneg z) (by positivity)).2 (by linarith))
    (Real.sqrt_nonneg _)

/-- The logarithmic gradient of the regularized radial exponential weight has norm
at most `|c|`, with no restriction on the sign of `c`. -/
theorem norm_fderiv_exp_mul_sqrt_add_norm_sq_le (c : ℝ) (hb : 0 < b) (z : E) :
    ‖fderiv ℝ (fun t : E ↦ Real.exp (c * √(b + ‖t‖ ^ 2))) z‖ ≤
      |c| * Real.exp (c * √(b + ‖z‖ ^ 2)) := by
  rw [norm_fderiv_exp_mul_sqrt_add_norm_sq c hb]
  exact mul_le_of_le_one_right (by positivity) (norm_div_sqrt_add_norm_sq_le_one hb.le z)

/-- A nonnegative weight whose logarithmic gradient is at most that of the radial exponential
weight, `|c| ‖z‖ / √(b + ‖z‖²)`, satisfies `‖dV‖² ≤ c² V²`. -/
theorem norm_fderiv_sq_le_of_norm_fderiv_le {V : E → ℝ} (c : ℝ) (hb : 0 ≤ b) {z : E}
    (hV : 0 ≤ V z) (hdV : ‖fderiv ℝ V z‖ ≤ |c| * (‖z‖ / √(b + ‖z‖ ^ 2)) * V z) :
    ‖fderiv ℝ V z‖ ^ 2 ≤ c ^ 2 * V z ^ 2 := by
  have h := hdV.trans (mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_right (abs_nonneg c) (norm_div_sqrt_add_norm_sq_le_one hb z)) hV)
  simpa only [mul_pow, sq_abs] using pow_le_pow_left₀ (norm_nonneg _) h 2

/-- The truncated radial exponential weight `W / (1 + ε W)`, `W = exp(c √(b + ‖z‖²))`, is smooth
for `ε ≥ 0`, of every order. -/
theorem contDiff_exp_div_one_add_mul_exp (c : ℝ) (hb : 0 < b) {ε : ℝ} (hε : 0 ≤ ε)
    {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun z : E ↦ Real.exp (c * √(b + ‖z‖ ^ 2)) /
      (1 + ε * Real.exp (c * √(b + ‖z‖ ^ 2)))) :=
  have hW := contDiff_exp_mul_sqrt_add_norm_sq (E := E) (n := n) c hb
  hW.div (contDiff_const.add (contDiff_const.mul hW)) fun _ ↦ by positivity

omit [InnerProductSpace ℝ E] in
/-- The truncated radial exponential weight `W / (1 + ε W)`, `ε ≥ 0`, is nonnegative. -/
theorem exp_div_one_add_mul_exp_nonneg (c : ℝ) {ε : ℝ} (hε : 0 ≤ ε) (z : E) :
    0 ≤ Real.exp (c * √(b + ‖z‖ ^ 2)) / (1 + ε * Real.exp (c * √(b + ‖z‖ ^ 2))) := by
  positivity

omit [InnerProductSpace ℝ E] in
/-- The truncated radial exponential weight `W / (1 + ε W)`, `ε ≥ 0`, is at most `W`. -/
theorem exp_div_one_add_mul_exp_le_exp (c : ℝ) {ε : ℝ} (hε : 0 ≤ ε) (z : E) :
    Real.exp (c * √(b + ‖z‖ ^ 2)) / (1 + ε * Real.exp (c * √(b + ‖z‖ ^ 2))) ≤
      Real.exp (c * √(b + ‖z‖ ^ 2)) :=
  div_le_self (Real.exp_pos _).le (le_add_of_nonneg_right (by positivity))

omit [InnerProductSpace ℝ E] in
/-- The truncated radial exponential weight `W / (1 + ε W)`, `ε > 0`, is bounded by `1 / ε`. -/
theorem exp_div_one_add_mul_exp_le_one_div (c : ℝ) {ε : ℝ} (hε : 0 < ε) (z : E) :
    Real.exp (c * √(b + ‖z‖ ^ 2)) / (1 + ε * Real.exp (c * √(b + ‖z‖ ^ 2))) ≤ 1 / ε := by
  rw [div_le_div_iff₀ (by positivity) hε]
  linarith [mul_comm (Real.exp (c * √(b + ‖z‖ ^ 2))) ε]

/-- The truncated radial exponential weight `W / (1 + ε W)`, `W = exp(c √(b + ‖z‖²))`, `ε ≥ 0`,
has logarithmic gradient at most that of `W`, namely `|c| ‖z‖ / √(b + ‖z‖²)`. -/
theorem norm_fderiv_exp_div_one_add_mul_exp_le (c : ℝ) (hb : 0 < b) {ε : ℝ} (hε : 0 ≤ ε)
    (z : E) :
    ‖fderiv ℝ (fun t : E ↦ Real.exp (c * √(b + ‖t‖ ^ 2)) /
        (1 + ε * Real.exp (c * √(b + ‖t‖ ^ 2)))) z‖ ≤
      |c| * (‖z‖ / √(b + ‖z‖ ^ 2)) *
        (Real.exp (c * √(b + ‖z‖ ^ 2)) / (1 + ε * Real.exp (c * √(b + ‖z‖ ^ 2)))) := by
  set W : E → ℝ := fun t ↦ Real.exp (c * √(b + ‖t‖ ^ 2))
  have hW : 0 < W z := Real.exp_pos _
  have hd : 0 < 1 + ε * W z := by positivity
  -- `W / (1 + ε W)` is `W` composed with `s ↦ s / (1 + ε s)`, of derivative `1 / (1 + ε s)²`.
  have hg : HasDerivAt (fun s : ℝ ↦ s / (1 + ε * s)) (1 / (1 + ε * W z) ^ 2) (W z) := by
    have h := (hasDerivAt_id' (W z)).div (((hasDerivAt_id' (W z)).const_mul ε).const_add 1)
      hd.ne'
    convert h using 1
    field_simp
    ring
  have hWd : HasFDerivAt W (fderiv ℝ W z) z :=
    ((contDiff_exp_mul_sqrt_add_norm_sq (n := 1) c hb).differentiable (by simp) z).hasFDerivAt
  have hVd : HasFDerivAt (fun t ↦ W t / (1 + ε * W t))
      ((1 / (1 + ε * W z) ^ 2) • fderiv ℝ W z) z := hg.comp_hasFDerivAt z hWd
  rw [hVd.fderiv, norm_smul, Real.norm_of_nonneg (by positivity),
    norm_fderiv_exp_mul_sqrt_add_norm_sq c hb]
  set d := 1 + ε * W z
  rw [show 1 / d ^ 2 * (|c| * W z * (‖z‖ / √(b + ‖z‖ ^ 2))) =
    |c| * (‖z‖ / √(b + ‖z‖ ^ 2)) * (W z / d) * (1 / d) by field_simp]
  refine mul_le_of_le_one_right (by positivity) ?_
  rw [div_le_one hd]
  nlinarith [mul_nonneg hε hW.le]

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

omit [InnerProductSpace ℝ E] in
/-- The squared form of `exp_mul_sqrt_add_norm_sq_le`, comparing the squared weights that enter
weighted `L²` norms. -/
theorem sq_exp_mul_sqrt_add_norm_sq_le (c s t : ℝ) (z : E) :
    Real.exp (c * √(s + ‖z‖ ^ 2)) ^ 2 ≤
      Real.exp (|c| * √|s - t|) ^ 2 * Real.exp (c * √(t + ‖z‖ ^ 2)) ^ 2 := by
  rw [← mul_pow]
  exact pow_le_pow_left₀ (Real.exp_pos _).le (exp_mul_sqrt_add_norm_sq_le c s t z) 2

end TauCeti
