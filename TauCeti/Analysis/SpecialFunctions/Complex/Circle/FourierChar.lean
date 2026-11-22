/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle

/-!
# Real Fourier characters and geometric exponential sums

This file records algebraic identities and closed-form trigonometric expressions for geometric
sums of Mathlib's real additive Fourier character `Real.fourierChar : AddChar ℝ Circle`:

* `Real.conj_fourierChar` and `Real.fourierChar_mul_fourierChar`: conjugation and multiplication of
  complex-valued `Real.fourierChar`.
* `Real.norm_sum_range_fourierChar_mul_abs_sin` and
  `Real.norm_sum_range_fourierChar_sq_eq_sin_div_sq`: closed forms for the norm of a geometric
  exponential sum in terms of `Real.sin`.
-/

public section

namespace Real

/-- Conjugating a complex-valued Fourier character negates its phase. -/
theorem conj_fourierChar (x : ℝ) :
    starRingEnd ℂ (Real.fourierChar x : ℂ) = (Real.fourierChar (-x) : ℂ) := by
  rw [← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv]

/-- Multiplying two complex-valued Fourier characters adds their phases. -/
theorem fourierChar_mul_fourierChar (x y : ℝ) :
    (Real.fourierChar x : ℂ) * (Real.fourierChar y : ℂ) = (Real.fourierChar (x + y) : ℂ) := by
  rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]

/-- Closed-form product identity for the norm of a geometric exponential sum:
`‖∑ k ∈ range M, Real.fourierChar (k * t)‖ * |sin (π * t)| = |sin (π * M * t)|`. -/
theorem norm_sum_range_fourierChar_mul_abs_sin (t : ℝ) (M : ℕ) :
    ‖∑ k ∈ Finset.range M, (Real.fourierChar ((k : ℝ) * t) : ℂ)‖ * |Real.sin (Real.pi * t)| =
      |Real.sin (Real.pi * (M : ℝ) * t)| := by
  let z : ℂ := (Real.fourierChar t : ℂ)
  have hpow : ∀ k : ℕ, (Real.fourierChar ((k : ℝ) * t) : ℂ) = z ^ k := by
    intro k
    rw [← Circle.coe_pow, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
  simp_rw [hpow]
  have hgeom := congrArg (fun w : ℂ ↦ ‖w‖) (geom_sum_mul z M)
  rw [norm_mul] at hgeom
  have hnorm_sub_one (s : ℝ) :
      ‖(Real.fourierChar s : ℂ) - 1‖ = 2 * |Real.sin (Real.pi * s)| := by
    have hs : (Real.fourierChar s : ℂ) = Complex.exp (Complex.I * ((2 * Real.pi * s : ℝ) : ℂ)) := by
      simp only [Real.fourierChar_apply, mul_comm]
    rw [hs, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul, abs_two]
    congr 3; ring
  have hz1 : ‖z - 1‖ = 2 * |Real.sin (Real.pi * t)| := hnorm_sub_one t
  have hzM : ‖z ^ M - 1‖ = 2 * |Real.sin (Real.pi * (M : ℝ) * t)| := by
    rw [← hpow M, hnorm_sub_one, mul_assoc]
  rw [hz1, hzM] at hgeom
  linarith

/-- Whenever `sin (π * t) ≠ 0`, the squared norm of the geometric exponential sum of length `M`
equals `(sin (π * M * t) / sin (π * t)) ^ 2`. -/
theorem norm_sum_range_fourierChar_sq_eq_sin_div_sq (t : ℝ) (M : ℕ)
    (ht : Real.sin (Real.pi * t) ≠ 0) :
    ‖∑ k ∈ Finset.range M, (Real.fourierChar ((k : ℝ) * t) : ℂ)‖ ^ 2 =
      (Real.sin (Real.pi * (M : ℝ) * t) / Real.sin (Real.pi * t)) ^ 2 := by
  have h := congrArg (fun r : ℝ ↦ r ^ 2) (t.norm_sum_range_fourierChar_mul_abs_sin M)
  rw [mul_pow, sq_abs, sq_abs] at h
  rw [div_pow, eq_div_iff (pow_ne_zero 2 ht)]
  exact h

end Real
