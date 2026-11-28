/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import TauCeti.RingTheory.Polynomial.Monic.Irreducible
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.Harmonic.Bounds
import TauCeti.FieldTheory.Finite.Irreducible.Count

/-!
# The reciprocal sum over monic irreducible polynomials of bounded degree

Let `K` be a finite field with `q` elements and let `N_q(j)` be the number of monic irreducible
polynomials of degree `j` over `K`. Since `j N_q(j) ≤ q ^ j`
(`Polynomial.mul_ncard_monicIrreduciblesOfDegree_le`), the sum of `q ^ (-deg J)` over the monic
irreducible `J` with `1 ≤ deg J ≤ ℓ`, which is `∑_{1 ≤ j ≤ ℓ} N_q(j) q ^ (-j)`, is at most the
harmonic sum `∑_{1 ≤ j ≤ ℓ} 1 / j ≤ 1 + log ℓ`. This is the function-field counterpart of the
elementary bound for the sum of the reciprocals of the primes, and the input on irreducibles to
Brun's sieve for polynomial vectors.

Both bounds are stated for an arbitrary field `K`. If `K` is infinite then `Nat.card K = 0`, every
term `N_q(j) / q ^ j` with `j ≥ 1` is `0` by the convention `x / 0 = 0`, and the bounds hold
trivially; the content is the case of a finite field.

## Main results

* `Polynomial.ncard_monicIrreduciblesOfDegree_div_pow_le`: `N_q(j) / q ^ j ≤ 1 / j`.
* `Polynomial.sum_Icc_ncard_monicIrreduciblesOfDegree_div_pow_le`:
  `∑_{1 ≤ j ≤ ℓ} N_q(j) / q ^ j ≤ 1 + log ℓ`.

## References

* L. Bary-Soroker, D. Koukoulopoulos, G. Kozma, *Irreducibility of random polynomials: general
  measures*, Invent. Math. 233 (2023), §6.1 and §8.
-/

public section

open Finset

namespace Polynomial

variable {K : Type*} [Field K]

/-- Over a field with `q` elements, the number `N_q(j)` of monic irreducible polynomials of degree
`j` satisfies `N_q(j) / q ^ j ≤ 1 / j`. For `j = 0` both sides are `0`, and for an infinite field
`K` the left side is `0` because `Nat.card K = 0`. -/
theorem ncard_monicIrreduciblesOfDegree_div_pow_le (j : ℕ) :
    ((monicIrreduciblesOfDegree K j).ncard : ℝ) / (Nat.card K : ℝ) ^ j ≤ 1 / j := by
  rcases eq_or_ne j 0 with rfl | hj
  · simp
  rcases finite_or_infinite K with hK | hK
  swap
  · simp [Nat.card_eq_zero_of_infinite, hj]
  have hj' : (0 : ℝ) < j := Nat.cast_pos.2 (Nat.pos_of_ne_zero hj)
  have hq : (0 : ℝ) < (Nat.card K : ℝ) ^ j := pow_pos (Nat.cast_pos.2 Nat.card_pos) j
  have hle : (j : ℝ) * (monicIrreduciblesOfDegree K j).ncard ≤ (Nat.card K : ℝ) ^ j := by
    exact_mod_cast mul_ncard_monicIrreduciblesOfDegree_le (K := K) j
  rw [div_le_div_iff₀ hq hj', one_mul, mul_comm]
  exact hle

/-- **The reciprocal sum over monic irreducibles of degree at most `ℓ`.** Over a field with `q`
elements, `∑_{1 ≤ j ≤ ℓ} N_q(j) / q ^ j ≤ 1 + log ℓ`, where `N_q(j)` is the number of monic
irreducible polynomials of degree `j`. The left side is the sum of `q ^ (-deg J)` over the monic
irreducible `J` with `1 ≤ deg J ≤ ℓ`. For an infinite field `K` every term is `0`. -/
theorem sum_Icc_ncard_monicIrreduciblesOfDegree_div_pow_le (ℓ : ℕ) :
    ∑ j ∈ Icc 1 ℓ, ((monicIrreduciblesOfDegree K j).ncard : ℝ) / (Nat.card K : ℝ) ^ j ≤
      1 + Real.log ℓ := by
  calc ∑ j ∈ Icc 1 ℓ, ((monicIrreduciblesOfDegree K j).ncard : ℝ) / (Nat.card K : ℝ) ^ j
      ≤ ∑ j ∈ Icc 1 ℓ, (1 : ℝ) / j :=
        sum_le_sum fun j _ ↦ ncard_monicIrreduciblesOfDegree_div_pow_le j
    _ = ((harmonic ℓ : ℚ) : ℝ) := by
        rw [harmonic_eq_sum_Icc]
        push_cast
        exact sum_congr rfl fun j _ ↦ one_div _
    _ ≤ 1 + Real.log ℓ := harmonic_le_one_add_log ℓ

/-! ### Examples -/

/-- Over `𝔽₂` there are two monic irreducible polynomials of degree one, so `j N₂(j) = 2 ^ j` at
`j = 1`. -/
example : (monicIrreduciblesOfDegree (ZMod 2) 1).ncard = 2 := by
  rw [ncard_monicIrreduciblesOfDegree_one, Nat.card_zmod]

/-- Over `𝔽₂` there is one monic irreducible polynomial of degree two, by Gauss's formula
`1 · N₂(1) + 2 · N₂(2) = 2 ^ 2`. It is `X ^ 2 + X + 1`. -/
example : (monicIrreduciblesOfDegree (ZMod 2) 2).ncard = 1 := by
  have h := sum_divisors_mul_ncard_monicIrreduciblesOfDegree (K := ZMod 2) two_ne_zero
  rw [Nat.prime_two.divisors, sum_pair (by decide), ncard_monicIrreduciblesOfDegree_one,
    Nat.card_zmod] at h
  omega

end Polynomial
