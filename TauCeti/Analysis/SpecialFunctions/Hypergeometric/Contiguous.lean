/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric

/-!
# Contiguous relations for Kummer's regularized function `𝐌(a, b, z)`

Kummer's regularized confluent hypergeometric function (Olver's `𝐌`, DLMF 13.2.4) is the singleton
case `Complex.regularizedHGFun {a} {b} z = ∑ (a)ₙ zⁿ / (n! Γ(b + n))` of Mathlib's generalized
regularized hypergeometric function. Because Mathlib's reciprocal Gamma function `(Gamma s)⁻¹`
vanishes at the nonpositive integer poles `s ∈ -ℕ` and satisfies the entire functional equation
`1 / Γ(s) = s / Γ(s + 1)`, every contiguous relation for `𝐌(a, b, z)` holds for *all* complex
parameters `a`, `b` and arguments `z`, with no pole exclusions.

From two termwise series identities — the upper-parameter difference
`𝐌(a + 1, b, z) - 𝐌(a, b, z) = z 𝐌(a + 1, b + 1, z)` (DLMF 13.3.4) and the mixed parameter
relation `𝐌(a, b, z) = (b - a) 𝐌(a, b + 1, z) + a 𝐌(a + 1, b + 1, z)` (DLMF 13.3.3) — two
diagonal contiguous relations follow by linear elimination.

## Main results

* `Complex.regularizedHGFun_add_one_left_sub` —
  `𝐌(a + 1, b, z) - 𝐌(a, b, z) = z 𝐌(a + 1, b + 1, z)` (DLMF 13.3.4).
* `Complex.regularizedHGFun_singleton_eq_sub_mul_add_mul` —
  `𝐌(a, b, z) = (b - a) 𝐌(a, b + 1, z) + a 𝐌(a + 1, b + 1, z)` (DLMF 13.3.3).
* `Complex.regularizedHGFun_singleton_eq_mul_add_mul` —
  `𝐌(a, b, z) = b 𝐌(a, b + 1, z) + a z 𝐌(a + 1, b + 2, z)` (from DLMF 13.3.3–13.3.4).
* `Complex.mul_regularizedHGFun_add_one_sub` —
  `b 𝐌(a + 1, b + 1, z) - 𝐌(a, b, z) = (b - a) z 𝐌(a + 1, b + 2, z)` (from DLMF 13.3.3–13.3.4).

## References

* *NIST Digital Library of Mathematical Functions*, [§13.2](https://dlmf.nist.gov/13.2) and
  [§13.3](https://dlmf.nist.gov/13.3).
-/

public section

noncomputable section

open scoped Nat

namespace Complex

/-- Upper-parameter difference for Kummer's regularized function (DLMF 13.3.4):
`𝐌(a + 1, b, z) - 𝐌(a, b, z) = z 𝐌(a + 1, b + 1, z)` for all complex `a`, `b`, `z`. -/
theorem regularizedHGFun_add_one_left_sub (a b z : ℂ) :
    regularizedHGFun {a + 1} {b} z - regularizedHGFun {a} {b} z =
      z * regularizedHGFun {a + 1} {b + 1} z := by
  have hdiff := (hasSum_regularizedHGFun (a := {a + 1}) (b := {b}) (by simp) z).sub
    (hasSum_regularizedHGFun (a := {a}) (b := {b}) (by simp) z)
  have hshift := (hasSum_nat_add_iff' 1).mpr hdiff
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, mul_one,
    regularizedHGFunCoeff_singleton, ascPochhammer_zero, Polynomial.eval_one, sub_self,
    sub_zero] at hshift
  refine hshift.unique ?_
  refine ((hasSum_regularizedHGFun (a := {a + 1}) (b := {b + 1}) (by simp) z).mul_left z).congr_fun
    fun n ↦ ?_
  have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast n.succ_ne_zero
  have hp : (ascPochhammer ℂ (n + 1)).eval (a + 1) - (ascPochhammer ℂ (n + 1)).eval a =
      (n + 1 : ℂ) * (ascPochhammer ℂ n).eval (a + 1) := by
    rw [ascPochhammer_succ_eval n (a + 1), ascPochhammer_succ_eval n a,
      ← ascPochhammer_eval_succ n a]
    ring
  simp only [regularizedHGFunCoeff_singleton]
  rw [← sub_mul, ← sub_div, hp, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one, show b + ((n : ℂ) + 1) = b + 1 + n by ring,
    pow_succ']
  field_simp

/-- **DLMF 13.3.3** for Kummer's regularized function:
`𝐌(a, b, z) = (b - a) 𝐌(a, b + 1, z) + a 𝐌(a + 1, b + 1, z)` for all complex `a`, `b`, `z`. -/
theorem regularizedHGFun_singleton_eq_sub_mul_add_mul (a b z : ℂ) :
    regularizedHGFun {a} {b} z =
      (b - a) * regularizedHGFun {a} {b + 1} z + a * regularizedHGFun {a + 1} {b + 1} z := by
  refine (hasSum_regularizedHGFun (a := {a}) (b := {b}) (by simp) z).unique ?_
  refine (((hasSum_regularizedHGFun (a := {a}) (b := {b + 1}) (by simp) z).mul_left (b - a)).add
    ((hasSum_regularizedHGFun (a := {a + 1}) (b := {b + 1}) (by simp) z).mul_left a)).congr_fun
    fun n ↦ ?_
  have hp := ascPochhammer_eval_succ n a
  have hG := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (b + n)
  simp only [regularizedHGFunCoeff_singleton, div_eq_mul_inv, mul_inv]
  rw [show b + 1 + (n : ℂ) = b + n + 1 by ring]
  symm
  calc (b - a) * ((ascPochhammer ℂ n).eval a * ((n ! : ℂ)⁻¹ * (Gamma (b + n + 1))⁻¹) * z ^ n) +
        a * ((ascPochhammer ℂ n).eval (a + 1) * ((n ! : ℂ)⁻¹ * (Gamma (b + n + 1))⁻¹) * z ^ n)
      = ((b - a) * (ascPochhammer ℂ n).eval a + a * (ascPochhammer ℂ n).eval (a + 1)) *
          ((n ! : ℂ)⁻¹ * (Gamma (b + n + 1))⁻¹ * z ^ n) := by ring
    _ = (ascPochhammer ℂ n).eval a * (n ! : ℂ)⁻¹ *
          ((b + n) * (Gamma (b + n + 1))⁻¹) * z ^ n := by rw [hp]; ring
    _ = (ascPochhammer ℂ n).eval a * ((n ! : ℂ)⁻¹ * (Gamma (b + n))⁻¹) * z ^ n := by
          rw [← hG]; ring

/-- First diagonal contiguous relation for Kummer's regularized function (from DLMF 13.3.3–13.3.4):
`𝐌(a, b, z) = b 𝐌(a, b + 1, z) + a z 𝐌(a + 1, b + 2, z)` for all complex `a`, `b`, `z`.
This is the confluent `₁F₁` counterpart of `Complex.regularizedHGFun_zero_singleton_eq_mul_add_mul`
for `₀F₁`. -/
theorem regularizedHGFun_singleton_eq_mul_add_mul (a b z : ℂ) :
    regularizedHGFun {a} {b} z =
      b * regularizedHGFun {a} {b + 1} z + a * z * regularizedHGFun {a + 1} {b + 2} z := by
  have h1 := regularizedHGFun_singleton_eq_sub_mul_add_mul a b z
  have h2 := regularizedHGFun_add_one_left_sub a (b + 1) z
  rw [show b + 1 + 1 = b + 2 by ring] at h2
  linear_combination h1 + a * h2

/-- Second diagonal contiguous relation for Kummer's regularized function (from DLMF 13.3.3–13.3.4):
`b 𝐌(a + 1, b + 1, z) - 𝐌(a, b, z) = (b - a) z 𝐌(a + 1, b + 2, z)` for all complex `a`, `b`, `z`. -/
theorem mul_regularizedHGFun_add_one_sub (a b z : ℂ) :
    b * regularizedHGFun {a + 1} {b + 1} z - regularizedHGFun {a} {b} z =
      (b - a) * z * regularizedHGFun {a + 1} {b + 2} z := by
  have h1 := regularizedHGFun_singleton_eq_sub_mul_add_mul a b z
  have h2 := regularizedHGFun_add_one_left_sub a (b + 1) z
  rw [show b + 1 + 1 = b + 2 by ring] at h2
  linear_combination (b - a) * h2 - h1

end Complex
