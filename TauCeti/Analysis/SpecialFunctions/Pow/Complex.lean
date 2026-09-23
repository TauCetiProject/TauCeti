/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Principal complex powers: positive real scaling and inversion on a sector

Multiplication of a complex number by a nonnegative real scalar is compatible with principal
complex powers.  Away from zero, this follows because positive scaling does not cross the branch
cut of the principal logarithm; the zero cases follow from the totalized definition of `cpow`.

Taking the principal power `u ^ (r⁻¹ : ℝ)` of a nonzero `u` divides its argument by `r`, so
raising the result back to the power `r` returns `u` — but only as long as the intermediate
argument stays inside the principal range `(-π, π]`, which is where `Complex.cpow_mul` may be
applied.  For a positive real exponent `r` that range is reached exactly on the sector
`-(r * π) < arg u ≤ r * π`.

## Main results

* `TauCeti.ofReal_mul_cpow` -- a principal power splits across a nonnegative real factor.
* `TauCeti.cpow_sum` -- a principal power of a finite sum splits into a product for a nonzero
  complex base.
* `TauCeti.cpow_inv_cpow_of_arg_mem_Ioc` -- raising an inverse principal power recovers its
  base on a suitable sector.
-/

public section

open Complex

namespace TauCeti

/-- A principal complex power splits across multiplication by a nonnegative real scalar:
`((r : ℂ) * z) ^ w = (r : ℂ) ^ w * z ^ w` for all complex `z` and `w`, without a branch
hypothesis on `z`.  This generalizes `Complex.mul_cpow_ofReal_nonneg` to a complex second factor;
the proof follows Mathlib's. -/
theorem ofReal_mul_cpow {r : ℝ} (hr : 0 ≤ r) (z w : ℂ) :
    ((r : ℂ) * z) ^ w = (r : ℂ) ^ w * z ^ w := by
  rcases eq_or_ne w 0 with (rfl | hw)
  · simp only [Complex.cpow_zero, mul_one]
  rcases eq_or_lt_of_le hr with (rfl | hr')
  · rw [Complex.ofReal_zero, zero_mul, Complex.zero_cpow hw, zero_mul]
  rcases eq_or_ne z 0 with (rfl | hz)
  · simp [Complex.zero_cpow hw]
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hr'.ne') hz),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr'.ne'),
    Complex.cpow_def_of_ne_zero hz, Complex.log_ofReal_mul hr' hz, add_mul, Complex.exp_add]
  rw [Complex.ofReal_log hr]

/-- A principal complex power with nonzero base takes a finite sum of exponents to the
corresponding product. -/
theorem cpow_sum {ι : Type*} {x : ℂ} (hx : x ≠ 0) (f : ι → ℂ) (s : Finset ι) :
    x ^ (∑ i ∈ s, f i) = ∏ i ∈ s, x ^ f i :=
  map_sum (⟨⟨fun y ↦ x ^ y, Complex.cpow_zero x⟩,
    fun y z ↦ Complex.cpow_add y z hx⟩ : ℂ →+ Additive ℂ) f s

/-- The principal power `u ^ (r⁻¹ : ℝ)` raised to the real power `r` is again `u`, for a
positive `r` and a base whose argument lies in the sector `(-(r * π), r * π]`.  The intermediate
argument `arg u / r` then lies in `(-π, π]`, so the principal branch is not crossed. -/
theorem cpow_inv_cpow_of_arg_mem_Ioc {u : ℂ} {r : ℝ} (hr : 0 < r)
    (harg : u.arg ∈ Set.Ioc (-(r * Real.pi)) (r * Real.pi)) :
    (u ^ ((r⁻¹ : ℝ) : ℂ)) ^ (r : ℂ) = u := by
  rw [← Complex.cpow_mul]
  · norm_num [hr.ne']
  · simp only [Complex.mul_im, Complex.log_im, ofReal_re, ofReal_im, mul_zero, zero_add]
    calc
      -Real.pi = (-(r * Real.pi)) * r⁻¹ := by field_simp
      _ < u.arg * r⁻¹ := mul_lt_mul_of_pos_right harg.1 (inv_pos.mpr hr)
  · simp only [Complex.mul_im, Complex.log_im, ofReal_re, ofReal_im, mul_zero, zero_add]
    calc
      u.arg * r⁻¹ ≤ (r * Real.pi) * r⁻¹ := mul_le_mul_of_nonneg_right harg.2 (inv_nonneg.mpr hr.le)
      _ = Real.pi := by field_simp

end TauCeti

end
