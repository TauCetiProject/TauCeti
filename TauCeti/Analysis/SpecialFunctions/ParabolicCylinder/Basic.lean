/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
import TauCeti.Analysis.SpecialFunctions.Hypergeometric.Kummer.Contiguous
import TauCeti.Analysis.SpecialFunctions.Hypergeometric.Kummer.HalfInteger
import TauCeti.Analysis.SpecialFunctions.Hypergeometric.Kummer.Transformation
import TauCeti.RingTheory.Polynomial.Pochhammer

/-!
# The even and odd solutions of Weber's equation

Write `𝐌(a, b, z) = Complex.regularizedHGFun {a} {b} z` for Olver's regularized Kummer function,
so that `Γ(b) 𝐌(a, b, z)` is Kummer's function `M(a, b, z)` for `b ∉ {0, −1, −2, …}`, in
particular for the lower parameters `b = ½` and `b = 3/2` used here. This file defines the even
and odd solutions of Weber's equation `w'' = (z²/4 + a) w` (DLMF 12.2.2),

`u₁(a, z) = e^{−z²/4} Γ(½) 𝐌(a/2 + ¼, ½, z²/2)`,
`u₂(a, z) = z e^{−z²/4} Γ(3/2) 𝐌(a/2 + ¾, 3/2, z²/2)`

(DLMF 12.7.12–12.7.13), and proves their Kummer-transformed forms and their power series
DLMF 12.4.3–12.4.6, for all complex `a` and `z`.

## Main definitions

* `TauCeti.parabolicCylinderEven`: the even solution `u₁(a, z)`.
* `TauCeti.parabolicCylinderOdd`: the odd solution `u₂(a, z)`.

## Main results

* `Complex.exp_neg_sq_div_four_mul_regularizedHGFun`: Kummer's transformation of
  `e^{−z²/4} 𝐌(c, b, z²/2)`, shared by the two solutions.
* `TauCeti.parabolicCylinderEven_eq_exp_mul`, `TauCeti.parabolicCylinderOdd_eq_exp_mul`: the
  Kummer-transformed forms `u₁(a, z) = e^{z²/4} Γ(½) 𝐌(¼ − a/2, ½, −z²/2)` and
  `u₂(a, z) = z e^{z²/4} Γ(3/2) 𝐌(¾ − a/2, 3/2, −z²/2)` (DLMF 12.7.12–12.7.13).
* `TauCeti.hasSum_parabolicCylinderEven`, `TauCeti.hasSum_parabolicCylinderOdd`: the power
  series DLMF 12.4.3–12.4.4, with the factor `e^{−z²/4}`.
* `TauCeti.hasSum_parabolicCylinderEven_exp_sq_div_four`,
  `TauCeti.hasSum_parabolicCylinderOdd_exp_sq_div_four`: the power series DLMF 12.4.5–12.4.6,
  with the factor `e^{z²/4}`.
* `TauCeti.parabolicCylinderEven_zero_right`, `TauCeti.parabolicCylinderOdd_zero_right`:
  `u₁(a, 0) = 1` and `u₂(a, 0) = 0`.
* `TauCeti.parabolicCylinderEven_neg_one_half`, `TauCeti.parabolicCylinderOdd_neg_three_halves`,
  `TauCeti.parabolicCylinderEven_inv_two`: `u₁(−½, z) = e^{−z²/4}`, `u₂(−3/2, z) = z e^{−z²/4}`
  and `u₁(½, z) = e^{z²/4}`.

## References

* *NIST Digital Library of Mathematical Functions*, [§12.4](https://dlmf.nist.gov/12.4) and
  [§12.7(iv)](https://dlmf.nist.gov/12.7.iv).

The definitions and series are adapted from the lean-DLMF project
(<https://github.com/bjbraams/lean-DLMF>), files `DLMF/ParabolicCylinder/Basic/Functions.lean` and
`DLMF/ParabolicCylinder/ElementaryProperties.lean`, where they are stated with the unregularized
Kummer function.
-/

public section

noncomputable section

open Complex

open scoped Nat

namespace Complex

/-- Kummer's transformation `𝐌(c, b, w) = e^w 𝐌(b − c, b, −w)` at `w = z²/2`, with the Weber factor
`e^{−z²/4}`: `e^{−z²/4} 𝐌(c, b, z²/2) = e^{z²/4} 𝐌(b − c, b, −z²/2)`. -/
theorem exp_neg_sq_div_four_mul_regularizedHGFun (c b z : ℂ) :
    exp (-z ^ 2 / 4) * regularizedHGFun {c} {b} (z ^ 2 / 2) =
      exp (z ^ 2 / 4) * regularizedHGFun {b - c} {b} (-(z ^ 2 / 2)) := by
  -- the exponents: `−z²/4 + z²/2 = z²/4`
  have he : -z ^ 2 / 4 + z ^ 2 / 2 = z ^ 2 / 4 := by ring
  rw [regularizedHGFun_singleton_eq_exp_mul, ← mul_assoc, ← exp_add, he]

end Complex

namespace TauCeti

/-- The even solution `u₁(a, z) = e^{−z²/4} M(a/2 + ¼, ½, z²/2)` of Weber's equation
(DLMF 12.7.12), with Kummer's function `M(a, ½, ·) = Γ(½) 𝐌(a, ½, ·)`. -/
def parabolicCylinderEven (a z : ℂ) : ℂ :=
  exp (-z ^ 2 / 4) * (Gamma (1 / 2) * regularizedHGFun {a / 2 + 1 / 4} {1 / 2} (z ^ 2 / 2))

/-- The odd solution `u₂(a, z) = z e^{−z²/4} M(a/2 + ¾, 3/2, z²/2)` of Weber's equation
(DLMF 12.7.13), with Kummer's function `M(a, 3/2, ·) = Γ(3/2) 𝐌(a, 3/2, ·)`. -/
def parabolicCylinderOdd (a z : ℂ) : ℂ :=
  z * exp (-z ^ 2 / 4) * (Gamma (3 / 2) * regularizedHGFun {a / 2 + 3 / 4} {3 / 2} (z ^ 2 / 2))

/-- The defining formula of the even solution `u₁(a, z)`. -/
theorem parabolicCylinderEven_def (a z : ℂ) :
    parabolicCylinderEven a z =
      exp (-z ^ 2 / 4) * (Gamma (1 / 2) * regularizedHGFun {a / 2 + 1 / 4} {1 / 2} (z ^ 2 / 2)) :=
  (rfl)

/-- The defining formula of the odd solution `u₂(a, z)`. -/
theorem parabolicCylinderOdd_def (a z : ℂ) :
    parabolicCylinderOdd a z = z * exp (-z ^ 2 / 4) *
      (Gamma (3 / 2) * regularizedHGFun {a / 2 + 3 / 4} {3 / 2} (z ^ 2 / 2)) :=
  (rfl)

/-- The Kummer-transformed form of the even solution (DLMF 12.7.12):
`u₁(a, z) = e^{z²/4} M(¼ − a/2, ½, −z²/2)`. -/
theorem parabolicCylinderEven_eq_exp_mul (a z : ℂ) :
    parabolicCylinderEven a z = exp (z ^ 2 / 4) *
      (Gamma (1 / 2) * regularizedHGFun {1 / 4 - a / 2} {1 / 2} (-(z ^ 2 / 2))) := by
  -- the transformed upper parameter
  have hc : (1 / 2 : ℂ) - (a / 2 + 1 / 4) = 1 / 4 - a / 2 := by ring
  rw [parabolicCylinderEven_def, mul_left_comm, exp_neg_sq_div_four_mul_regularizedHGFun, hc,
    mul_left_comm]

/-- The Kummer-transformed form of the odd solution (DLMF 12.7.13):
`u₂(a, z) = z e^{z²/4} M(¾ − a/2, 3/2, −z²/2)`. -/
theorem parabolicCylinderOdd_eq_exp_mul (a z : ℂ) :
    parabolicCylinderOdd a z = z * exp (z ^ 2 / 4) *
      (Gamma (3 / 2) * regularizedHGFun {3 / 4 - a / 2} {3 / 2} (-(z ^ 2 / 2))) := by
  -- the transformed upper parameter
  have hc : (3 / 2 : ℂ) - (a / 2 + 3 / 4) = 3 / 4 - a / 2 := by ring
  rw [parabolicCylinderOdd_def, mul_assoc z, mul_assoc z, mul_left_comm (exp _),
    exp_neg_sq_div_four_mul_regularizedHGFun, hc, mul_left_comm (exp _)]

/-- **The power series DLMF 12.4.3** of the even solution:
`u₁(a, z) = e^{−z²/4} ∑ₖ (∏_{r<k} (a + ½ + 2r)) z^{2k} / (2k)!`. -/
theorem hasSum_parabolicCylinderEven (a z : ℂ) :
    HasSum (fun k : ℕ => exp (-z ^ 2 / 4) * (∏ r ∈ Finset.range k, (a + 1 / 2 + 2 * r)) *
      z ^ (2 * k) / ((2 * k)! : ℂ)) (parabolicCylinderEven a z) := by
  rw [parabolicCylinderEven_def]
  refine ((hasSum_Gamma_one_half_mul_regularizedHGFun (a / 2 + 1 / 4) (z ^ 2 / 2)).mul_left
    (exp (-z ^ 2 / 4))).congr_fun fun k => ?_
  -- the upper parameter is `(a + ½)/2`, and the argument `4 (z²/2) = 2 z²`
  have hc : (a + 1 / 2) / 2 = a / 2 + 1 / 4 := by ring
  have hw : 4 * (z ^ 2 / 2) = 2 * z ^ 2 := by ring
  rw [Finset.prod_congr rfl fun (r : ℕ) _ => add_comm (a + 1 / 2) (2 * (r : ℂ)),
    ← two_pow_mul_ascPochhammer_eval_div_two, hc, hw, mul_pow, pow_mul]
  ring

/-- **The power series DLMF 12.4.4** of the odd solution:
`u₂(a, z) = e^{−z²/4} ∑ₖ (∏_{r<k} (a + 3/2 + 2r)) z^{2k+1} / (2k+1)!`. -/
theorem hasSum_parabolicCylinderOdd (a z : ℂ) :
    HasSum (fun k : ℕ => exp (-z ^ 2 / 4) * (∏ r ∈ Finset.range k, (a + 3 / 2 + 2 * r)) *
      z ^ (2 * k + 1) / ((2 * k + 1)! : ℂ)) (parabolicCylinderOdd a z) := by
  rw [parabolicCylinderOdd_def]
  refine ((hasSum_Gamma_three_halves_mul_regularizedHGFun (a / 2 + 3 / 4) (z ^ 2 / 2)).mul_left
    (z * exp (-z ^ 2 / 4))).congr_fun fun k => ?_
  -- the upper parameter is `(a + 3/2)/2`, and the argument `4 (z²/2) = 2 z²`
  have hc : (a + 3 / 2) / 2 = a / 2 + 3 / 4 := by ring
  have hw : 4 * (z ^ 2 / 2) = 2 * z ^ 2 := by ring
  rw [Finset.prod_congr rfl fun (r : ℕ) _ => add_comm (a + 3 / 2) (2 * (r : ℂ)),
    ← two_pow_mul_ascPochhammer_eval_div_two, hc, hw, mul_pow]
  ring

/-- **The power series DLMF 12.4.5** of the even solution, from its Kummer-transformed form:
`u₁(a, z) = e^{z²/4} ∑ₖ (∏_{r<k} (a − ½ − 2r)) z^{2k} / (2k)!`. -/
theorem hasSum_parabolicCylinderEven_exp_sq_div_four (a z : ℂ) :
    HasSum (fun k : ℕ => exp (z ^ 2 / 4) * (∏ r ∈ Finset.range k, (a - 1 / 2 - 2 * r)) *
      z ^ (2 * k) / ((2 * k)! : ℂ)) (parabolicCylinderEven a z) := by
  rw [parabolicCylinderEven_eq_exp_mul]
  refine ((hasSum_Gamma_one_half_mul_regularizedHGFun (1 / 4 - a / 2) (-(z ^ 2 / 2))).mul_left
    (exp (z ^ 2 / 4))).congr_fun fun k => ?_
  -- the upper parameter is `−(a − ½)/2`, and the argument `4 (−z²/2) = −2 z²`
  have hc : -(a - 1 / 2) / 2 = 1 / 4 - a / 2 := by ring
  have hw : 4 * -(z ^ 2 / 2) = -2 * z ^ 2 := by ring
  rw [prod_range_sub_two_mul, hc, hw, mul_pow, pow_mul]
  ring

/-- **The power series DLMF 12.4.6** of the odd solution, from its Kummer-transformed form:
`u₂(a, z) = e^{z²/4} ∑ₖ (∏_{r<k} (a − 3/2 − 2r)) z^{2k+1} / (2k+1)!`. -/
theorem hasSum_parabolicCylinderOdd_exp_sq_div_four (a z : ℂ) :
    HasSum (fun k : ℕ => exp (z ^ 2 / 4) * (∏ r ∈ Finset.range k, (a - 3 / 2 - 2 * r)) *
      z ^ (2 * k + 1) / ((2 * k + 1)! : ℂ)) (parabolicCylinderOdd a z) := by
  rw [parabolicCylinderOdd_eq_exp_mul]
  refine ((hasSum_Gamma_three_halves_mul_regularizedHGFun (3 / 4 - a / 2)
    (-(z ^ 2 / 2))).mul_left (z * exp (z ^ 2 / 4))).congr_fun fun k => ?_
  -- the upper parameter is `−(a − 3/2)/2`, and the argument `4 (−z²/2) = −2 z²`
  have hc : -(a - 3 / 2) / 2 = 3 / 4 - a / 2 := by ring
  have hw : 4 * -(z ^ 2 / 2) = -2 * z ^ 2 := by ring
  rw [prod_range_sub_two_mul, hc, hw, mul_pow]
  ring

/-- The even solution at the origin: `u₁(a, 0) = 1`. -/
@[simp]
theorem parabolicCylinderEven_zero_right (a : ℂ) : parabolicCylinderEven a 0 = 1 := by
  have hΓ : Gamma (1 / 2) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  rw [parabolicCylinderEven_def, zero_pow two_ne_zero, zero_div, regularizedHGFun_zero,
    regularizedHGFunCoeff_singleton_zero, mul_inv_cancel₀ hΓ]
  simp

/-- The odd solution at the origin: `u₂(a, 0) = 0`. -/
@[simp]
theorem parabolicCylinderOdd_zero_right (a : ℂ) : parabolicCylinderOdd a 0 = 0 := by
  simp [parabolicCylinderOdd_def]

/-- At `a = −½` the series DLMF 12.4.3 terminates: `u₁(−½, z) = e^{−z²/4}`. -/
@[simp]
theorem parabolicCylinderEven_neg_one_half (z : ℂ) :
    parabolicCylinderEven (-1 / 2) z = exp (-z ^ 2 / 4) := by
  have hΓ : Gamma (1 / 2) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  -- the upper parameter `−½/2 + ¼` vanishes
  have hc : (-1 / 2 : ℂ) / 2 + 1 / 4 = 0 := by norm_num
  rw [parabolicCylinderEven_def, hc, regularizedHGFun_zero_singleton, mul_inv_cancel₀ hΓ, mul_one]

/-- At `a = −3/2` the series DLMF 12.4.4 terminates: `u₂(−3/2, z) = z e^{−z²/4}`. -/
@[simp]
theorem parabolicCylinderOdd_neg_three_halves (z : ℂ) :
    parabolicCylinderOdd (-3 / 2) z = z * exp (-z ^ 2 / 4) := by
  have hΓ : Gamma (3 / 2) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  -- the upper parameter `−3/2/2 + ¾` vanishes
  have hc : (-3 / 2 : ℂ) / 2 + 3 / 4 = 0 := by norm_num
  rw [parabolicCylinderOdd_def, hc, regularizedHGFun_zero_singleton, mul_inv_cancel₀ hΓ, mul_one]

/-- At `a = ½` the series DLMF 12.4.5 terminates: `u₁(½, z) = e^{z²/4}`. The parameter is written
`2⁻¹`, the form to which `simp` normalizes `1 / 2`. -/
@[simp]
theorem parabolicCylinderEven_inv_two (z : ℂ) :
    parabolicCylinderEven 2⁻¹ z = exp (z ^ 2 / 4) := by
  have hΓ : Gamma (1 / 2) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  -- the transformed upper parameter `¼ − ½/2` vanishes
  have hc : (1 / 4 : ℂ) - 2⁻¹ / 2 = 0 := by norm_num
  rw [parabolicCylinderEven_eq_exp_mul, hc, regularizedHGFun_zero_singleton, mul_inv_cancel₀ hΓ,
    mul_one]

end TauCeti
