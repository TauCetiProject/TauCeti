/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.GaussSum

/-!
# Trigonometric expansions of complex Gauss sums

`MulChar.gaussSum_eq_sum_mul_re_add_I_mul_sum_mul_im` splits Mathlib's `gaussSum` into a sum
for each component of the additive character. Since `AddChar.map_neg_eq_conj` makes those
components even and odd, the imaginary component cancels for an even multiplicative character
(`MulChar.gaussSum_eq_sum_mul_re_of_even`) and the real component cancels for an odd one
(`MulChar.gaussSum_eq_I_mul_sum_mul_im_of_odd`). For Dirichlet characters these are the
cancellations in C. Pomerance, *Remarks on the Pólya–Vinogradov inequality*, equations (8)–(9).
-/

public section

open Finset

namespace MulChar

variable {R : Type*} [CommRing R] [Fintype R] (χ : MulChar R ℂ) (e : AddChar R ℂ)

/-- The Gauss sum is the weighted sum of the real parts of the additive character plus
`Complex.I` times the weighted sum of its imaginary parts. -/
theorem gaussSum_eq_sum_mul_re_add_I_mul_sum_mul_im :
    gaussSum χ e = (∑ b : R, χ b * (e b).re) + Complex.I * ∑ b : R, χ b * (e b).im := by
  simp only [gaussSum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun b _ ↦ ?_
  calc
    _ = χ b * ((e b).re + (e b).im * Complex.I) := by rw [Complex.re_add_im]
    _ = _ := by ring

/-- The Gauss sum of an even multiplicative character uses only the real parts of the additive
character. -/
theorem gaussSum_eq_sum_mul_re_of_even (hχ : Function.Even (χ : R → ℂ)) :
    gaussSum χ e = ∑ b : R, χ b * (e b).re := by
  have him : Function.Odd (fun b : R ↦ χ b * ((e b).im : ℂ)) := by
    intro b
    simp only [hχ.eq, AddChar.map_neg_eq_conj, Complex.conj_im, Complex.ofReal_neg, mul_neg]
  rw [χ.gaussSum_eq_sum_mul_re_add_I_mul_sum_mul_im, him.sum_eq_zero, mul_zero, add_zero]

/-- The Gauss sum of an odd multiplicative character uses only the imaginary parts of the additive
character, with a factor of `Complex.I`. -/
theorem gaussSum_eq_I_mul_sum_mul_im_of_odd (hχ : Function.Odd (χ : R → ℂ)) :
    gaussSum χ e = Complex.I * ∑ b : R, χ b * (e b).im := by
  have hre : Function.Odd (fun b : R ↦ χ b * ((e b).re : ℂ)) := by
    intro b
    simp only [hχ.eq, AddChar.map_neg_eq_conj, Complex.conj_re, neg_mul]
  rw [χ.gaussSum_eq_sum_mul_re_add_I_mul_sum_mul_im, hre.sum_eq_zero, zero_add]

end MulChar
