/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric

/-!
# Contiguous relations and differentiation of Kummer's regularized function `𝐌(a, b, z)`

Kummer's regularized confluent hypergeometric function (Olver's `𝐌`, DLMF 13.2.4) is the singleton
case `Complex.regularizedHGFun {a} {b} z = ∑ (a)ₙ zⁿ / (n! Γ(b + n))` of Mathlib's generalized
regularized hypergeometric function. Because Mathlib's reciprocal Gamma function `(Gamma s)⁻¹`
vanishes at the nonpositive integer poles `s ∈ -ℕ` and satisfies the entire functional equation
`1 / Γ(s) = s / Γ(s + 1)`, every contiguous relation and derivative formula for `𝐌(a, b, z)` holds
for *all* complex parameters `a`, `b` and arguments `z`, with no pole exclusions.

From two termwise series identities — the upper-parameter difference
`𝐌(a + 1, b, z) - 𝐌(a, b, z) = z 𝐌(a + 1, b + 1, z)` and the mixed parameter relation
`𝐌(a, b, z) = (b - a) 𝐌(a, b + 1, z) + a 𝐌(a + 1, b + 1, z)` (DLMF 13.3.3) — the remaining
contiguous relations (DLMF 13.3.1, 13.3.2, 13.3.4) follow by pure linear elimination.

## Main results

* `Complex.regularizedHGFunCoeff_singleton` — the coefficient `(a)ₙ / (n! Γ(b + n))` of
  `𝐌(a, b, z)`.
* `Complex.regularizedHGFun_singleton_zero_left` — `𝐌(0, b, z) = (Γ b)⁻¹`.
* `Complex.hasDerivAt_regularizedHGFun_singleton`, `Complex.deriv_regularizedHGFun_singleton` —
  `∂𝐌(a, b, z)/∂z = a 𝐌(a + 1, b + 1, z)` (DLMF 13.3.15).
* `Complex.regularizedHGFun_add_one_left_sub` —
  `𝐌(a + 1, b, z) - 𝐌(a, b, z) = z 𝐌(a + 1, b + 1, z)` (DLMF 13.3.4, difference form).
* `Complex.regularizedHGFun_singleton_eq_sub_mul_add_mul` —
  `𝐌(a, b, z) = (b - a) 𝐌(a, b + 1, z) + a 𝐌(a + 1, b + 1, z)` (DLMF 13.3.3).
* `Complex.regularizedHGFun_singleton_eq_mul_add_mul` —
  `𝐌(a, b, z) = b 𝐌(a, b + 1, z) + a z 𝐌(a + 1, b + 2, z)` (DLMF 13.3.4).
* `Complex.mul_regularizedHGFun_add_one_sub` —
  `b 𝐌(a + 1, b + 1, z) - 𝐌(a, b, z) = (b - a) z 𝐌(a + 1, b + 2, z)`.
* `Complex.regularizedHGFun_singleton_eq_add_mul_sub_mul` — the three-term `b`-contiguous relation
  `𝐌(a, b, z) = (b + z) 𝐌(a, b + 1, z) - (b + 1 - a) z 𝐌(a, b + 2, z)` (DLMF 13.3.2).
* `Complex.sub_mul_regularizedHGFun_add_mul_eq` — the three-term `a`-contiguous relation
  `(b - a - 1) 𝐌(a, b, z) + (2a + 2 - b + z) 𝐌(a + 1, b, z) = (a + 1) 𝐌(a + 2, b, z)`
  (DLMF 13.3.1).

## References

* *NIST Digital Library of Mathematical Functions*, [§13.2](https://dlmf.nist.gov/13.2) and
  [§13.3](https://dlmf.nist.gov/13.3).
-/

public section

noncomputable section

open scoped Nat

namespace Complex

/-- The `n`-th power-series coefficient of Kummer's regularized function `𝐌(a, b, z)` is
`(a)ₙ / (n! Γ(b + n))`. -/
@[simp]
theorem regularizedHGFunCoeff_singleton (a b : ℂ) (n : ℕ) :
    regularizedHGFunCoeff {a} {b} n = (ascPochhammer ℂ n).eval a / (n ! * Gamma (b + n)) := by
  simp [regularizedHGFunCoeff]

/-- At `a = 0`, Kummer's regularized function reduces to the constant `𝐌(0, b, z) = (Γ b)⁻¹`
(DLMF 13.6.1), including at `b ∈ -ℕ` where both sides vanish. -/
@[simp]
theorem regularizedHGFun_singleton_zero_left (b z : ℂ) :
    regularizedHGFun {0} {b} z = (Gamma b)⁻¹ := by
  have h := (hasSum_nat_add_iff' 1).mpr (hasSum_regularizedHGFun (a := {0}) (b := {b}) (by simp) z)
  rw [Finset.range_one, Finset.sum_singleton, pow_zero, mul_one,
    regularizedHGFunCoeff_singleton, ascPochhammer_zero, Polynomial.eval_one, Nat.factorial_zero,
    Nat.cast_one, one_mul, Nat.cast_zero, add_zero, one_div] at h
  have hzero : HasSum (fun n : ℕ ↦ regularizedHGFunCoeff {0} {b} (n + 1) * z ^ (n + 1)) 0 := by
    convert hasSum_zero (α := ℂ) (β := ℕ) with n
    rw [regularizedHGFunCoeff_singleton, ascPochhammer_succ_left, Polynomial.eval_mul,
      Polynomial.eval_X, zero_mul, zero_div, zero_mul]
  linear_combination h.unique hzero

/-- The derivative of Kummer's regularized function in its argument (DLMF 13.3.15):
`∂𝐌(a, b, z)/∂z = a 𝐌(a + 1, b + 1, z)`. -/
theorem hasDerivAt_regularizedHGFun_singleton (a b z : ℂ) :
    HasDerivAt (regularizedHGFun {a} {b}) (a * regularizedHGFun {a + 1} {b + 1} z) z := by
  have hcard : ({a} : Multiset ℂ).card ≤ ({b} : Multiset ℂ).card := by simp
  have hd := (analyticAt_regularizedHGFun_of_card_le hcard z).differentiableAt.hasDerivAt
  suffices hderiv : deriv (regularizedHGFun {a} {b}) z =
      a * regularizedHGFun {a + 1} {b + 1} z by rwa [hderiv] at hd
  refine (hasSum_deriv_regularizedHGFun hcard z).unique ?_
  refine ((hasSum_regularizedHGFun (a := {a + 1}) (b := {b + 1}) (by simp) z).mul_left a).congr_fun
    fun n ↦ ?_
  have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast n.succ_ne_zero
  have hp : (ascPochhammer ℂ (n + 1)).eval a = a * (ascPochhammer ℂ n).eval (a + 1) := by
    rw [ascPochhammer_succ_left, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_comp,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  simp only [regularizedHGFunCoeff_singleton, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, hp]
  rw [show b + ((n : ℂ) + 1) = b + 1 + n by ring]
  field_simp

/-- The derivative of `𝐌(a, b, ·)` as a function (DLMF 13.3.15):
`deriv (𝐌(a, b, ·)) z = a 𝐌(a + 1, b + 1, z)`. -/
@[simp]
theorem deriv_regularizedHGFun_singleton (a b : ℂ) :
    deriv (regularizedHGFun {a} {b}) = fun z ↦ a * regularizedHGFun {a + 1} {b + 1} z :=
  funext fun z ↦ (hasDerivAt_regularizedHGFun_singleton a b z).deriv

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
    have h1 : (ascPochhammer ℂ (n + 1)).eval (a + 1) =
        (ascPochhammer ℂ n).eval (a + 1) * (a + 1 + n) := by simp [ascPochhammer_succ_right]
    have h2 : (ascPochhammer ℂ (n + 1)).eval a = a * (ascPochhammer ℂ n).eval (a + 1) := by
      rw [ascPochhammer_succ_left, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_comp,
        Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
    rw [h1, h2]; ring
  simp only [regularizedHGFunCoeff_singleton]
  rw [← sub_mul, ← sub_div, hp, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one, show b + ((n : ℂ) + 1) = b + 1 + n by ring,
    pow_succ']
  field_simp

/-- At `a = 1`, `𝐌(1, b, z) = (Γ b)⁻¹ + z 𝐌(1, b + 1, z)` for all complex `b` and `z`. -/
theorem regularizedHGFun_one_singleton_eq (b z : ℂ) :
    regularizedHGFun {1} {b} z = (Gamma b)⁻¹ + z * regularizedHGFun {1} {b + 1} z := by
  have h := regularizedHGFun_add_one_left_sub 0 b z
  rw [zero_add, regularizedHGFun_singleton_zero_left] at h
  linear_combination h

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

/-- **DLMF 13.3.4** for Kummer's regularized function:
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

/-- **DLMF 13.3.2** for Kummer's regularized function (three-term `b`-contiguous relation):
`𝐌(a, b, z) = (b + z) 𝐌(a, b + 1, z) - (b + 1 - a) z 𝐌(a, b + 2, z)` for all complex `a`, `b`,
`z`. -/
theorem regularizedHGFun_singleton_eq_add_mul_sub_mul (a b z : ℂ) :
    regularizedHGFun {a} {b} z =
      (b + z) * regularizedHGFun {a} {b + 1} z -
        (b + 1 - a) * z * regularizedHGFun {a} {b + 2} z := by
  have h1 := regularizedHGFun_singleton_eq_mul_add_mul a b z
  have h2 := regularizedHGFun_singleton_eq_sub_mul_add_mul a (b + 1) z
  rw [show b + 1 + 1 = b + 2 by ring] at h2
  linear_combination h1 - z * h2

/-- **DLMF 13.3.1** for Kummer's regularized function (three-term `a`-contiguous relation):
`(b - a - 1) 𝐌(a, b, z) + (2a + 2 - b + z) 𝐌(a + 1, b, z) = (a + 1) 𝐌(a + 2, b, z)` for all
complex `a`, `b`, `z`. -/
theorem sub_mul_regularizedHGFun_add_mul_eq (a b z : ℂ) :
    (b - a - 1) * regularizedHGFun {a} {b} z +
      (2 * a + 2 - b + z) * regularizedHGFun {a + 1} {b} z =
      (a + 1) * regularizedHGFun {a + 2} {b} z := by
  have h1 := regularizedHGFun_singleton_eq_sub_mul_add_mul (a + 1) b z
  have h2 := regularizedHGFun_add_one_left_sub a b z
  have h3 := regularizedHGFun_add_one_left_sub (a + 1) b z
  rw [show a + 1 + 1 = a + 2 by ring] at h1 h3
  linear_combination z * h1 - (b - a - 1) * h2 - (a + 1) * h3

end Complex
