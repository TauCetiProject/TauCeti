/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.EulerProduct.Basic
public import Mathlib.NumberTheory.LSeries.Basic

/-!
# Euler products of degree two

Let `a : ℕ → ℂ` be multiplicative on coprime arguments with `a 1 = 1`, and suppose that along
the powers of every prime `p` it satisfies a second-order linear recurrence

`a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - d p * a (p ^ r)`.

Then, wherever its Dirichlet series converges absolutely, it has the Euler product of degree two

`L(a, s) = ∏ₚ (1 - a p * p ^ (-s) + d p * p ^ (-2 s))⁻¹`.

The multiplicativity reduces this to Mathlib's general Euler product
`EulerProduct.eulerProduct_hasProd`, and the recurrence evaluates each local sum
`∑ₑ a (p ^ e) p ^ (-e s)` as the inverse of the quadratic polynomial in `p ^ (-s)`.

This is the shape of the L-function of a normalised Hecke eigenform, where `d p = χ(p) p ^ (k - 1)`
(Diamond–Shurman, Theorem 5.9.2), but nothing here is specific to modular forms.

## Main results

* `TauCeti.LSeries.tsum_term_prime_pow_eq_inv`: the local factor at a prime.
* `TauCeti.LSeries.eulerProduct_hasProd_of_prime_pow_recurrence`,
  `TauCeti.LSeries.eulerProduct_tprod_of_prime_pow_recurrence`: the Euler product.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §5.9.
-/

public section

open Complex LSeries

namespace TauCeti.LSeries

/-- The Dirichlet term at a prime power is the coefficient times a power of `p ^ (-s)`. -/
theorem term_prime_pow (a : ℕ → ℂ) (s : ℂ) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    term a s (p ^ e) = a (p ^ e) * ((p : ℂ) ^ (-s)) ^ e := by
  simp [term_of_ne_zero (pow_ne_zero e hp.ne_zero), ← natCast_cpow_natCast_mul, cpow_nat_mul,
    cpow_neg, div_eq_mul_inv]

/-- The Dirichlet terms of a function multiplicative on coprime arguments are multiplicative on
coprime arguments. -/
theorem term_mul_of_coprime {a : ℕ → ℂ} (s : ℂ)
    (hmul : ∀ {m n : ℕ}, m.Coprime n → a (m * n) = a m * a n) {m n : ℕ} (hmn : m.Coprime n) :
    term a s (m * n) = term a s m * term a s n := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [term_of_ne_zero (mul_ne_zero hm hn), term_of_ne_zero hm, term_of_ne_zero hn, hmul hmn,
    Nat.cast_mul, natCast_mul_natCast_cpow, mul_div_mul_comm]

/-- **The local factor of a degree-two Euler product.** If `a 1 = 1` and along the powers of the
prime `p` the coefficients satisfy `a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - d * a (p ^ r)`, then
if the terms at the powers of `p` are summable, they sum to
`(1 - a p * p ^ (-s) + d * p ^ (-2 s))⁻¹`. -/
theorem tsum_term_prime_pow_eq_inv {a : ℕ → ℂ} {d s : ℂ} {p : ℕ} (hp : p.Prime) (h₁ : a 1 = 1)
    (hrec : ∀ r : ℕ, a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - d * a (p ^ r))
    (hs : Summable fun e : ℕ ↦ term a s (p ^ e)) :
    ∑' e : ℕ, term a s (p ^ e) = (1 - a p * (p : ℂ) ^ (-s) + d * (p : ℂ) ^ (-2 * s))⁻¹ := by
  set x : ℂ := (p : ℂ) ^ (-s)
  -- `cpow_nat_mul` expects the natural multiplier on the left of the complex exponent.
  have h_exp : -2 * s = (2 : ℕ) * -s := by push_cast; ring
  have hx : (p : ℂ) ^ (-2 * s) = x ^ 2 := by
    rw [h_exp, cpow_nat_mul]
  set u : ℕ → ℂ := fun e ↦ term a s (p ^ e)
  have hu : Summable u := hs
  have hu₁ : Summable fun e ↦ u (e + 1) := (summable_nat_add_iff 1).mpr hu
  -- the recurrence, read on the terms
  have hstep (e : ℕ) : u (e + 2) = a p * x * u (e + 1) - d * x ^ 2 * u e := by
    simp only [u, term_prime_pow a s hp, hrec]
    ring
  have h₀ : u 0 = 1 := by simp [u, term_prime_pow a s hp, h₁]
  have h₁' : u 1 = a p * x := by simp only [u, x, term_prime_pow a s hp, pow_one]
  -- peel off the first two terms and resum the tail with the recurrence
  have htail : ∑' e, u (e + 2) = a p * x * ∑' e, u (e + 1) - d * x ^ 2 * ∑' e, u e := by
    rw [tsum_congr hstep, (hu₁.mul_left _).tsum_sub (hu.mul_left _), tsum_mul_left, tsum_mul_left]
  have hS₁ : ∑' e, u e = u 0 + ∑' e, u (e + 1) := hu.tsum_eq_zero_add
  have hS₂ : ∑' e, u (e + 1) = u 1 + ∑' e, u (e + 2) := hu₁.tsum_eq_zero_add
  rw [hx]
  refine eq_inv_of_mul_eq_one_left ?_
  rw [h₀] at hS₁
  rw [h₁', htail] at hS₂
  linear_combination (1 - a p * x) * hS₁ + hS₂

/-- **The Euler product of degree two**, as a `HasProd`. Let `a` be multiplicative on coprime
arguments with `a 1 = 1`, satisfying at every prime `p` the recurrence
`a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - d p * a (p ^ r)`. Wherever its Dirichlet series
converges absolutely,
`L(a, s) = ∏ₚ (1 - a p * p ^ (-s) + d p * p ^ (-2 s))⁻¹`. -/
theorem eulerProduct_hasProd_of_prime_pow_recurrence {a d : ℕ → ℂ} {s : ℂ} (h₁ : a 1 = 1)
    (hmul : ∀ {m n : ℕ}, m.Coprime n → a (m * n) = a m * a n)
    (hrec : ∀ p : ℕ, p.Prime → ∀ r : ℕ,
      a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - d p * a (p ^ r))
    (hs : LSeriesSummable a s) :
    HasProd (fun p : Nat.Primes ↦ (1 - a p * (p : ℂ) ^ (-s) + d p * (p : ℂ) ^ (-2 * s))⁻¹)
      (LSeries a s) := by
  have h := EulerProduct.eulerProduct_hasProd (f := term a s) (by simp [h₁])
    (term_mul_of_coprime s hmul) hs.norm (term_zero a s)
  rw [LSeries]
  convert h using 2 with p
  exact (tsum_term_prime_pow_eq_inv p.prop h₁ (hrec p p.prop)
    (hs.comp_injective (Nat.pow_right_injective p.prop.two_le))).symm

/-- **The Euler product of degree two**, as a `tprod`: see
`TauCeti.LSeries.eulerProduct_hasProd_of_prime_pow_recurrence`. -/
theorem eulerProduct_tprod_of_prime_pow_recurrence {a d : ℕ → ℂ} {s : ℂ} (h₁ : a 1 = 1)
    (hmul : ∀ {m n : ℕ}, m.Coprime n → a (m * n) = a m * a n)
    (hrec : ∀ p : ℕ, p.Prime → ∀ r : ℕ,
      a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - d p * a (p ^ r))
    (hs : LSeriesSummable a s) :
    ∏' p : Nat.Primes, (1 - a p * (p : ℂ) ^ (-s) + d p * (p : ℂ) ^ (-2 * s))⁻¹ =
      LSeries a s :=
  (eulerProduct_hasProd_of_prime_pow_recurrence h₁ hmul hrec hs).tprod_eq

end TauCeti.LSeries
