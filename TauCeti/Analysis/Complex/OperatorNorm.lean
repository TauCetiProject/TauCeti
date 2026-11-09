/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.OperatorNorm
import TauCeti.LinearAlgebra.Complex.Module

/-!
# Bounds for real-linear maps out of the complex line

The values on `1` and `I` determine a continuous real-linear map on every complex vector
(`ContinuousLinearMap.apply_eq_re_smul_one_add_im_smul_I`), and control its norm there. This
estimate turns a Cauchy--Riemann equation into a bound on the full differential: if
`L I = A (L 1)` with `‖A‖ ≤ M`, then `‖L a‖ ≤ (1 + M) * ‖L 1‖ * ‖a‖`
(`ContinuousLinearMap.norm_apply_le_of_apply_I_eq`). For a real-valued `L` the two values
determine the norm exactly, `‖L‖ ^ 2 = L 1 ^ 2 + L I ^ 2`
(`ContinuousLinearMap.norm_sq_eq_apply_one_sq_add_apply_I_sq`): the norm of the differential of
a real function on the plane is the length of its gradient.
-/

public section

namespace ContinuousLinearMap

/-- A continuous real-linear map out of the complex plane is evaluated in the real basis
`(1,I)`. -/
theorem apply_eq_re_smul_one_add_im_smul_I {F : Type*} [TopologicalSpace F] [AddCommMonoid F]
    [Module ℝ F] (L : ℂ →L[ℝ] F) (z : ℂ) : L z = z.re • L 1 + z.im • L Complex.I :=
  L.toLinearMap.apply_eq_re_smul_one_add_im_smul_I z

/-- Bound a real-linear map on a complex vector by its values on the standard real basis. -/
theorem norm_apply_le_norm_one_add_norm_I {V : Type*} [SeminormedAddCommGroup V]
    [NormedSpace ℝ V] (L : ℂ →L[ℝ] V) (z : ℂ) :
    ‖L z‖ ≤ (‖L 1‖ + ‖L Complex.I‖) * ‖z‖ := by
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    simp [Complex.real_smul]
  calc
    ‖L z‖ = ‖z.re • L 1 + z.im • L Complex.I‖ := by
      conv_lhs => rw [hz, map_add, map_smul, map_smul]
    _ ≤ ‖z.re‖ * ‖L 1‖ + ‖z.im‖ * ‖L Complex.I‖ := by
      simpa only [norm_smul] using norm_add_le (z.re • L 1) (z.im • L Complex.I)
    _ ≤ ‖z‖ * ‖L 1‖ + ‖z‖ * ‖L Complex.I‖ := by
      gcongr
      · exact Complex.abs_re_le_norm z
      · exact Complex.abs_im_le_norm z
    _ = (‖L 1‖ + ‖L Complex.I‖) * ‖z‖ := by ring

/-- If a real-linear map out of `ℂ` sends `I` to `A (L 1)`, where `‖A‖ ≤ M`, then `L 1` controls
`L`: `‖L a‖ ≤ (1 + M) * ‖L 1‖ * ‖a‖`. -/
theorem norm_apply_le_of_apply_I_eq {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    {L : ℂ →L[ℝ] V} {A : V →L[ℝ] V} {M : ℝ} (hL : L Complex.I = A (L 1)) (hA : ‖A‖ ≤ M)
    (a : ℂ) : ‖L a‖ ≤ (1 + M) * ‖L 1‖ * ‖a‖ := by
  refine (L.norm_apply_le_norm_one_add_norm_I a).trans
    (mul_le_mul_of_nonneg_right ?_ (norm_nonneg a))
  rw [hL]
  linarith [A.le_of_opNorm_le hA (L 1)]

/-- The norm of a real-valued continuous real-linear map on the complex plane is the Euclidean
length of its values on the real basis `(1, I)`: `‖L‖ ^ 2 = L 1 ^ 2 + L I ^ 2`. -/
theorem norm_sq_eq_apply_one_sq_add_apply_I_sq (L : ℂ →L[ℝ] ℝ) :
    ‖L‖ ^ 2 = L 1 ^ 2 + L Complex.I ^ 2 := by
  set a := L 1
  set b := L Complex.I
  have hL (z : ℂ) : L z = z.re * a + z.im * b := by
    simpa [smul_eq_mul] using L.apply_eq_re_smul_one_add_im_smul_I z
  have hle : ‖L‖ ≤ √(a ^ 2 + b ^ 2) := by
    refine L.opNorm_le_bound (Real.sqrt_nonneg _) fun z ↦ ?_
    rw [hL, Real.norm_eq_abs, Complex.norm_def, ← Real.sqrt_mul (by positivity),
      Complex.normSq_apply]
    refine Real.abs_le_sqrt ?_
    nlinarith [sq_nonneg (z.re * b - z.im * a)]
  -- The bound is attained at `z = a + b I`.
  have hge : √(a ^ 2 + b ^ 2) ≤ ‖L‖ := by
    have hz := L.le_opNorm ⟨a, b⟩
    have hn : ‖(⟨a, b⟩ : ℂ)‖ = √(a ^ 2 + b ^ 2) := by
      rw [Complex.norm_def, Complex.normSq_apply]
      ring_nf
    rw [hL, Real.norm_eq_abs, hn, abs_of_nonneg (by simp only; nlinarith)] at hz
    have hs : a * a + b * b = √(a ^ 2 + b ^ 2) * √(a ^ 2 + b ^ 2) := by
      rw [Real.mul_self_sqrt (by positivity)]
      ring
    simp only at hz
    rcases (Real.sqrt_nonneg (a ^ 2 + b ^ 2)).eq_or_lt with h0 | hpos
    · rw [← h0]
      exact norm_nonneg _
    · exact le_of_mul_le_mul_right (hs ▸ hz) hpos
  rw [le_antisymm hle hge, Real.sq_sqrt (by positivity)]

end ContinuousLinearMap

end
