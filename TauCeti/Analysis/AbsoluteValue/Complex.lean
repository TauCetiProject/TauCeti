/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
import TauCeti.Analysis.SpecialFunctions.Pow.Real

/-!
# Absolute values on `ℂ` extending the absolute value of `ℝ`

An absolute value on `ℂ` whose restriction to `ℝ` is the usual absolute value is the complex
norm. No continuity is assumed. Writing `z = re z + im z * I` with `N I = 1` bounds `N` by twice the
norm; multiplicativity applied to the powers of `z` removes the factor `2`, and
`z * conj z = ‖z‖ ^ 2` gives the reverse inequality.

This is what turns an `ℝ`-algebra isomorphism of a normed field with `ℂ`, as produced by the
Gelfand–Mazur theorem, into an isometry.

## Main results

* `AbsoluteValue.eq_norm_of_apply_ofReal`: an absolute value on `ℂ` agreeing with `|·|` on `ℝ` is
  the complex norm.
-/

public section

namespace AbsoluteValue

/-- An absolute value on `ℂ` that restricts to the usual absolute value on `ℝ` is the complex
norm. -/
theorem eq_norm_of_apply_ofReal (N : AbsoluteValue ℂ ℝ) (h : ∀ r : ℝ, N r = |r|) (z : ℂ) :
    N z = ‖z‖ := by
  have hI : N Complex.I = 1 := by
    refine (pow_left_inj₀ (N.nonneg _) zero_le_one two_ne_zero).mp ?_
    rw [one_pow, sq, ← map_mul, Complex.I_mul_I, map_neg_eq_map, map_one]
  have hle_two (z : ℂ) : N z ≤ 2 * ‖z‖ := by
    calc N z = N (z.re + z.im * Complex.I) := by rw [Complex.re_add_im]
      _ ≤ N z.re + N (z.im * Complex.I) := N.add_le _ _
      _ = |z.re| + |z.im| := by rw [map_mul, hI, mul_one, h, h]
      _ ≤ 2 * ‖z‖ := by linarith [Complex.abs_re_le_norm z, Complex.abs_im_le_norm z]
  have hle (z : ℂ) : N z ≤ ‖z‖ := by
    rcases eq_or_ne z 0 with rfl | hz
    · simp
    have hz' : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hdiv : N z / ‖z‖ ≤ 1 := Real.le_one_of_forall_pow_le_mul_rpow (C := 2) (s := 0)
      fun n ↦ by
        rw [div_pow, ← map_pow, ← norm_pow, Real.rpow_zero, mul_one,
          div_le_iff₀ (norm_pos_iff.mpr (pow_ne_zero n hz))]
        exact hle_two _
    rwa [div_le_one hz'] at hdiv
  refine (hle z).antisymm ?_
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  have hconj : N z * N ((starRingEnd ℂ) z) = ‖z‖ * ‖z‖ := by
    rw [← map_mul, Complex.mul_conj, h, Complex.normSq_eq_norm_sq, abs_of_nonneg (by positivity),
      sq]
  have hconj_le : N ((starRingEnd ℂ) z) ≤ ‖z‖ := (hle _).trans_eq (Complex.norm_conj z)
  nlinarith [norm_pos_iff.mpr hz, N.nonneg z]

end AbsoluteValue
