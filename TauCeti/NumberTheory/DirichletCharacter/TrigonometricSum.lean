/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.GaussSum
public import TauCeti.NumberTheory.DirichletCharacter.IntervalSum
import TauCeti.NumberTheory.GaussSum.Trigonometric

/-!
# Trigonometric expansions of Dirichlet character sums

Combining `gaussSum_mulShift_of_isPrimitive` with `MulChar.gaussSum_eq_sum_mul_re_of_even`
and `MulChar.gaussSum_eq_I_mul_sum_mul_im_of_odd` gives
`DirichletCharacter.Even.intervalSum_mul_gaussSum_eq_sum_re` and
`DirichletCharacter.Odd.intervalSum_mul_gaussSum_eq_I_mul_sum_im` for primitive characters.
For the standard additive character, the real and imaginary parts of its values give the
cosine and sine kernels used in the parity-sensitive Pólya–Vinogradov inequality.

See C. Pomerance, *Remarks on the Pólya–Vinogradov inequality*, equations (8)–(10).
-/

public section

open Finset

namespace DirichletCharacter

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- The cosine expansion of the interval sum of an even primitive character, multiplied by
the Gauss sum of its inverse. -/
theorem Even.intervalSum_mul_gaussSum_eq_sum_re (hχ : χ.Even) (hprim : χ.IsPrimitive)
    (e : AddChar (ZMod q) ℂ) (M : ℤ) (N : ℕ) :
    χ.intervalSum M N * gaussSum χ⁻¹ e =
      ∑ b : ZMod q, χ⁻¹ b * ∑ n ∈ Ioc M (M + N), (e ((n : ZMod q) * b)).re := by
  have hneg : χ (-1) = 1 := hχ
  have hinv : χ⁻¹.Even := by
    simp only [Even, MulChar.inv_apply_eq_inv', hneg, inv_one]
  have hshift (a : ZMod q) : gaussSum χ⁻¹ (e.mulShift a) = χ a * gaussSum χ⁻¹ e := by
    simpa only [inv_inv] using gaussSum_mulShift_of_isPrimitive e hprim.inv a
  rw [intervalSum_def, sum_mul]
  simp_rw [← hshift, MulChar.gaussSum_eq_sum_mul_re_of_even χ⁻¹ _ hinv.to_fun,
    AddChar.mulShift_apply]
  rw [sum_comm]
  simp only [Complex.ofReal_sum, mul_sum]

/-- The sine expansion of the interval sum of an odd primitive character, multiplied by
the Gauss sum of its inverse. -/
theorem Odd.intervalSum_mul_gaussSum_eq_I_mul_sum_im (hχ : χ.Odd) (hprim : χ.IsPrimitive)
    (e : AddChar (ZMod q) ℂ) (M : ℤ) (N : ℕ) :
    χ.intervalSum M N * gaussSum χ⁻¹ e =
      Complex.I * ∑ b : ZMod q, χ⁻¹ b * ∑ n ∈ Ioc M (M + N), (e ((n : ZMod q) * b)).im := by
  have hneg : χ (-1) = -1 := hχ
  have hinv : χ⁻¹.Odd := by
    simp only [Odd, MulChar.inv_apply_eq_inv', hneg, inv_neg, inv_one]
  have hshift (a : ZMod q) : gaussSum χ⁻¹ (e.mulShift a) = χ a * gaussSum χ⁻¹ e := by
    simpa only [inv_inv] using gaussSum_mulShift_of_isPrimitive e hprim.inv a
  rw [intervalSum_def, sum_mul]
  simp_rw [← hshift, MulChar.gaussSum_eq_I_mul_sum_mul_im_of_odd χ⁻¹ _ hinv.to_fun,
    AddChar.mulShift_apply]
  rw [← mul_sum, sum_comm]
  simp only [Complex.ofReal_sum, mul_sum]

end DirichletCharacter
