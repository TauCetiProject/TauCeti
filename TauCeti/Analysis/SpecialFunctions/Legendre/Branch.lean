/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# Domains and branches of the Legendre functions

The Ferrers functions of the first and second kind (DLMF 14.3.1, 14.3.12) are holomorphic on the
doubly cut plane `D = {z | 1 - z ∈ slitPlane ∧ 1 + z ∈ slitPlane} = ℂ \ ((-∞, -1] ∪ [1, ∞))`, and
the associated Legendre functions `P^μ_ν(z)`, `Q^μ_ν(z)` and Olver's `𝑸^μ_ν(z)` on the cut plane
`U = {z | z - 1 ∈ slitPlane} = ℂ \ (-∞, 1]`. Their definitions multiply a Gauss hypergeometric
function by principal powers: of `(1 + z) / (1 - z)` and of `1 - z²` on `D`, and of
`(z + 1) / (z - 1)`, `z - 1`, `z + 1` and `z` on `U`; the argument of the hypergeometric function is
`(1 - z) / 2` or `z²` on `D`, and `(1 - z) / 2` or `z⁻²` on `U`. The slit-plane memberships of these
bases and arguments, and the topology of `D` and `U`, are in `TauCeti.Analysis.Complex.SlitPlane`.
This file proves that each power prefactor is holomorphic on its domain, that the argument
`(1 - z) / 2` lies in the cut plane `{w | 1 - w ∈ slitPlane}` of the hypergeometric function, and
the branch identities between these powers: on all of `D` for `(1 - z²)^s` and
`((1 + z) / (1 - z))^s`, on all of `U` for `((z + 1) / (z - 1))^s`, and on the right half-plane
`0 < re z` for `(z² - 1)^s`.

## Main results

* `Complex.one_sub_sq_cpow`, `Complex.one_add_div_one_sub_cpow`: on `D`,
  `(1 - z²)^s = (1 - z)^s (1 + z)^s` and `((1 + z) / (1 - z))^s = (1 + z)^s (1 - z)^(-s)`.
* `Complex.add_one_div_sub_one_cpow`: on `U`, `((z + 1) / (z - 1))^s = (z + 1)^s (z - 1)^(-s)`.
* `Complex.sq_sub_one_cpow`: for `0 < re z`, `(z² - 1)^s = (z - 1)^s (z + 1)^s`, so the product
  `(z - 1)^s (z + 1)^s`, which is holomorphic on `U`, is the principal power on the right
  half-plane, and on `[1, ∞)` the principal power of the nonnegative real `x² - 1`
  (`Complex.ofReal_sub_one_cpow_mul_ofReal_add_one_cpow`). On the left half-plane the principal
  `(z² - 1)^s` jumps across the imaginary axis, which is why the definition of `𝑸^μ_ν` uses the
  product.
* `Complex.differentiableOn_one_add_div_one_sub_cpow`, `Complex.differentiableOn_one_sub_sq_cpow`,
  `Complex.differentiableOn_add_one_div_sub_one_cpow`,
  `Complex.differentiableOn_sub_one_cpow_mul_add_one_cpow`: the power prefactors are holomorphic on
  their domains.

## References

* F. W. J. Olver, *Asymptotics and Special Functions*, Ch. 5, §12.2 and §15.1.
* NIST *Digital Library of Mathematical Functions*, §14.3 and §14.21(i).
-/

public section

open Set

namespace Complex

/-! ### The doubly cut plane `ℂ \ ((-∞, -1] ∪ [1, ∞))` -/

/-- The argument `(1 - z) / 2` of the hypergeometric function in the Ferrers function of the first
kind and in `P^μ_ν(z)` lies in its cut plane exactly when `1 + z` lies in the slit plane. -/
theorem one_sub_one_sub_div_two_mem_slitPlane_iff {z : ℂ} :
    1 - (1 - z) / 2 ∈ slitPlane ↔ 1 + z ∈ slitPlane := by
  rw [show 1 - (1 - z) / 2 = (1 + z) / 2 by ring]
  simp [mem_slitPlane_iff]

/-- On the doubly cut plane, the principal power of `1 - z²` splits:
`(1 - z²)^s = (1 - z)^s (1 + z)^s`. -/
theorem one_sub_sq_cpow {z : ℂ} (hz₁ : 1 - z ∈ slitPlane) (hz₂ : 1 + z ∈ slitPlane) (s : ℂ) :
    (1 - z ^ 2) ^ s = (1 - z) ^ s * (1 + z) ^ s := by
  rw [show 1 - z ^ 2 = (1 - z) * (1 + z) by ring]
  refine TauCeti.mul_cpow_of_arg_add_mem (Ioo_subset_Ioc_self
    (arg_add_arg_mem_Ioo_of_im_mul_nonpos hz₁ hz₂ ?_)) s
  simp only [sub_im, one_im, add_im, zero_sub, zero_add, neg_mul, neg_nonpos]
  exact mul_self_nonneg _

/-- On the doubly cut plane, the principal power of the Möbius quotient splits:
`((1 + z) / (1 - z))^s = (1 + z)^s (1 - z)^(-s)`. -/
theorem one_add_div_one_sub_cpow {z : ℂ} (hz₁ : 1 - z ∈ slitPlane) (hz₂ : 1 + z ∈ slitPlane)
    (s : ℂ) : ((1 + z) / (1 - z)) ^ s = (1 + z) ^ s * (1 - z) ^ (-s) := by
  refine TauCeti.div_cpow_of_arg_div_add_arg_mem (slitPlane_ne_zero hz₁) (Ioo_subset_Ioc_self
    (arg_add_arg_mem_Ioo_of_im_mul_nonpos (one_add_div_one_sub_mem_slitPlane_iff.2 ⟨hz₁, hz₂⟩)
      hz₁ ?_)) s
  -- the imaginary part of the quotient is `2 * im z / ‖1 - z‖²`
  rw [div_im]
  simp only [add_im, sub_im, one_im, add_re, sub_re, one_re, zero_add, zero_sub]
  rw [← sub_div, div_mul_eq_mul_div]
  exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg z.im]) (normSq_nonneg _)

/-- `z ↦ ((1 + z) / (1 - z))^s` is holomorphic on the doubly cut plane. -/
theorem differentiableOn_one_add_div_one_sub_cpow (s : ℂ) :
    DifferentiableOn ℂ (fun z : ℂ => ((1 + z) / (1 - z)) ^ s)
      {z | 1 - z ∈ slitPlane ∧ 1 + z ∈ slitPlane} := by
  refine DifferentiableOn.cpow_const ?_ fun z hz => one_add_div_one_sub_mem_slitPlane_iff.2 hz
  exact ((differentiableOn_const 1).add differentiableOn_id).div
    ((differentiableOn_const 1).sub differentiableOn_id) fun z hz => slitPlane_ne_zero hz.1

/-- `z ↦ (1 - z²)^s` is holomorphic on the doubly cut plane. -/
theorem differentiableOn_one_sub_sq_cpow (s : ℂ) :
    DifferentiableOn ℂ (fun z : ℂ => (1 - z ^ 2) ^ s)
      {z | 1 - z ∈ slitPlane ∧ 1 + z ∈ slitPlane} :=
  ((differentiableOn_const 1).sub (differentiableOn_id.pow 2)).cpow_const
    fun _ hz => one_sub_sq_mem_slitPlane_iff.2 hz

/-! ### The cut plane `ℂ \ (-∞, 1]` -/

/-- On the cut plane `ℂ \ (-∞, 1]`, the principal power of `(z + 1) / (z - 1)` splits:
`((z + 1) / (z - 1))^s = (z + 1)^s (z - 1)^(-s)`. -/
theorem add_one_div_sub_one_cpow {z : ℂ} (hz : z - 1 ∈ slitPlane) (s : ℂ) :
    ((z + 1) / (z - 1)) ^ s = (z + 1) ^ s * (z - 1) ^ (-s) := by
  refine TauCeti.div_cpow_of_arg_div_add_arg_mem (slitPlane_ne_zero hz) (Ioo_subset_Ioc_self
    (arg_add_arg_mem_Ioo_of_im_mul_nonpos (add_one_div_sub_one_mem_slitPlane hz) hz ?_)) s
  -- the imaginary part of the quotient is `-2 * im z / ‖z - 1‖²`
  rw [div_im]
  simp only [add_im, sub_im, one_im, add_re, sub_re, one_re, add_zero, sub_zero]
  rw [← sub_div, div_mul_eq_mul_div]
  exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg z.im]) (normSq_nonneg _)

/-- In the right half-plane the product `(z - 1)^s (z + 1)^s` is the principal power of
`z² - 1`. -/
theorem sq_sub_one_cpow {z : ℂ} (hre : 0 < z.re) (s : ℂ) :
    (z ^ 2 - 1) ^ s = (z - 1) ^ s * (z + 1) ^ s := by
  rw [show z ^ 2 - 1 = (z - 1) * (z + 1) by ring]
  exact TauCeti.mul_cpow_of_arg_add_mem (arg_sub_one_add_arg_add_one_mem_Ioc hre) s

/-- On `[1, ∞)` the product `(x - 1)^s (x + 1)^s` is the principal power of the nonnegative real
number `x² - 1`. -/
theorem ofReal_sub_one_cpow_mul_ofReal_add_one_cpow {x : ℝ} (hx : 1 ≤ x) (s : ℂ) :
    ((x : ℂ) - 1) ^ s * ((x : ℂ) + 1) ^ s = ((x ^ 2 - 1 : ℝ) : ℂ) ^ s := by
  rw [← sq_sub_one_cpow (by simp; linarith), ofReal_sub, ofReal_pow, ofReal_one]

/-- `z ↦ ((z + 1) / (z - 1))^s` is holomorphic on the cut plane `ℂ \ (-∞, 1]`. -/
theorem differentiableOn_add_one_div_sub_one_cpow (s : ℂ) :
    DifferentiableOn ℂ (fun z : ℂ => ((z + 1) / (z - 1)) ^ s) {z | z - 1 ∈ slitPlane} := by
  refine DifferentiableOn.cpow_const ?_ fun z hz => add_one_div_sub_one_mem_slitPlane hz
  exact (differentiableOn_id.add (differentiableOn_const 1)).div
    (differentiableOn_id.sub (differentiableOn_const 1)) fun z hz => slitPlane_ne_zero hz

/-- `z ↦ (z - 1)^s (z + 1)^s` is holomorphic on the cut plane `ℂ \ (-∞, 1]`. -/
theorem differentiableOn_sub_one_cpow_mul_add_one_cpow (s : ℂ) :
    DifferentiableOn ℂ (fun z : ℂ => (z - 1) ^ s * (z + 1) ^ s) {z | z - 1 ∈ slitPlane} :=
  ((differentiableOn_id.sub (differentiableOn_const 1)).cpow_const fun _ hz => hz).mul
    ((differentiableOn_id.add (differentiableOn_const 1)).cpow_const
      fun _ hz => add_one_mem_slitPlane_of_sub_one_mem_slitPlane hz)

end Complex
