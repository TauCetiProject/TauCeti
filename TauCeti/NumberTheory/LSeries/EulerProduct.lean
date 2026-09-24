/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.EulerProduct.Basic
public import Mathlib.NumberTheory.LSeries.Basic
public import TauCeti.Topology.Algebra.InfiniteSum.LinearRecurrence

/-!
# Euler products with quadratic local factors

Let `a : ℕ → ℂ` be multiplicative on coprime arguments with `a 1 = 1`, and suppose that along the
powers of every prime `p` its values obey the second-order recurrence

`a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - c p * a (p ^ r)`.

Wherever the L-series of `a` converges absolutely, it is then the Euler product

`L(a, s) = ∏_p (1 - a p * p ^ (-s) + c p * p ^ (-2 s))⁻¹`.

At each prime, the quadratic factor times the sum of the prime-power terms is `1`. Thus each
factor is nonzero, and its inverse is the local contribution to the Euler product.

This is the shape of the L-function of a normalized Hecke eigenform, where `c p = χ(p) p^(k-1)`
(Diamond–Shurman, Theorem 5.9.2), and it covers the completely multiplicative case `c = 0`.

## Main results

* `TauCeti.LSeries_localFactor_mul_tsum_eq_one_of_recurrence`: the factor identity.
* `TauCeti.LSeries_localFactor_tsum_of_recurrence`: the prime-power sum is the inverse factor.
* `TauCeti.LSeries_localFactor_ne_zero_of_recurrence`: each quadratic factor is nonzero.
* `TauCeti.LSeries_eulerProduct_hasProd_of_recurrence`: the Euler product, as a `HasProd`.
* `TauCeti.LSeries_eulerProduct_tprod_of_recurrence`: the same, as an equality with `∏'`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  §5.9.
-/

public section

open LSeries Nat

namespace TauCeti

variable {a c : ℕ → ℂ} {s : ℂ}

/-- The quadratic factor times the sum over powers of a prime is `1` whenever the
prime-power coefficients satisfy the second-order recurrence. -/
theorem LSeries_localFactor_mul_tsum_eq_one_of_recurrence (h₁ : a 1 = 1) (p : Primes)
    (hrec : ∀ r : ℕ,
      a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - c p * a (p ^ r))
    (hs : Summable (fun e : ℕ ↦ term a s (p ^ e))) :
    (1 - a p * (p : ℂ) ^ (-s) + c p * (p : ℂ) ^ (-2 * s)) *
      (∑' e : ℕ, term a s (p ^ e)) = 1 := by
  have hterm (e : ℕ) : term a s (p ^ e) = a (p ^ e) * ((p : ℂ) ^ (-s)) ^ e := by
    rw [term_of_ne_zero (pow_ne_zero e p.prop.ne_zero), cast_pow,
      ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul, Complex.cpow_neg, inv_pow,
      div_eq_mul_inv]
  have key := hs.hasSum
    |>.one_sub_add_mul_eq_of_linearRec₂ (D := a p * (p : ℂ) ^ (-s))
      (S := c p * ((p : ℂ) ^ (-s)) ^ 2) fun r ↦ by
        simp only [hterm, hrec r]; ring
  rw [hterm 0, hterm 1] at key
  -- Convert the exponent to a natural multiple before applying `Complex.cpow_nat_mul`.
  have hexponent : -2 * s = (2 : ℕ) * -s := by push_cast; ring
  rw [hexponent, Complex.cpow_nat_mul]
  exact key.trans (by simp [h₁])

/-- The sum over powers of a prime is the inverse quadratic Euler factor. -/
@[simp]
theorem LSeries_localFactor_tsum_of_recurrence (h₁ : a 1 = 1) (p : Primes)
    (hrec : ∀ r : ℕ,
      a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - c p * a (p ^ r))
    (hs : Summable (fun e : ℕ ↦ term a s (p ^ e))) :
    ∑' e : ℕ, term a s (p ^ e) =
      (1 - a p * (p : ℂ) ^ (-s) + c p * (p : ℂ) ^ (-2 * s))⁻¹ :=
  eq_inv_of_mul_eq_one_right (LSeries_localFactor_mul_tsum_eq_one_of_recurrence h₁ p hrec hs)

/-- Each quadratic Euler factor is nonzero when its prime-power series converges. -/
theorem LSeries_localFactor_ne_zero_of_recurrence (h₁ : a 1 = 1) (p : Primes)
    (hrec : ∀ r : ℕ,
      a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - c p * a (p ^ r))
    (hs : Summable (fun e : ℕ ↦ term a s (p ^ e))) :
    1 - a p * (p : ℂ) ^ (-s) + c p * (p : ℂ) ^ (-2 * s) ≠ 0 := by
  intro hzero
  have h := LSeries_localFactor_mul_tsum_eq_one_of_recurrence h₁ p hrec hs
  rw [hzero] at h
  simp at h

/-- **The Euler product with quadratic local factors.** Let `a : ℕ → ℂ` satisfy `a 1 = 1`, be
multiplicative on coprime arguments, and obey the recurrence
`a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - c p * a (p ^ r)` along the powers of every prime `p`.
Where its L-series converges absolutely,

`∏_p (1 - a p * p ^ (-s) + c p * p ^ (-2 s))⁻¹ = L(a, s)`. -/
theorem LSeries_eulerProduct_hasProd_of_recurrence (h₁ : a 1 = 1)
    (hmul : ∀ {m n : ℕ}, m.Coprime n → a (m * n) = a m * a n)
    (hrec : ∀ p : ℕ, p.Prime → ∀ r : ℕ,
      a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - c p * a (p ^ r))
    (hs : LSeriesSummable a s) :
    HasProd (fun p : Primes ↦ (1 - a p * (p : ℂ) ^ (-s) + c p * (p : ℂ) ^ (-2 * s))⁻¹)
      (LSeries a s) := by
  have hterm₁ : term a s 1 = 1 := by
    simp [h₁]
  have htermMul : ∀ {m n : ℕ}, m.Coprime n → term a s (m * n) = term a s m * term a s n := by
    intro m n hmn
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    rw [term_of_ne_zero (mul_ne_zero hm hn), term_of_ne_zero hm, term_of_ne_zero hn, hmul hmn,
      cast_mul, Complex.natCast_mul_natCast_cpow, mul_div_mul_comm]
  have hlocal (p : Primes) : ∑' e : ℕ, term a s (p ^ e) =
      (1 - a p * (p : ℂ) ^ (-s) + c p * (p : ℂ) ^ (-2 * s))⁻¹ := by
    exact LSeries_localFactor_tsum_of_recurrence h₁ p (hrec p p.prop)
      (hs.comp_injective (Nat.pow_right_injective p.prop.two_le))
  have H := EulerProduct.eulerProduct_hasProd hterm₁ htermMul hs.norm (term_zero a s)
  rwa [funext hlocal] at H

/-- **The Euler product with quadratic local factors**, as an equality with `∏'`: under the
hypotheses of `TauCeti.LSeries_eulerProduct_hasProd_of_recurrence`,
`∏' p, (1 - a p * p ^ (-s) + c p * p ^ (-2 s))⁻¹ = L(a, s)`. -/
@[simp]
theorem LSeries_eulerProduct_tprod_of_recurrence (h₁ : a 1 = 1)
    (hmul : ∀ {m n : ℕ}, m.Coprime n → a (m * n) = a m * a n)
    (hrec : ∀ p : ℕ, p.Prime → ∀ r : ℕ,
      a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - c p * a (p ^ r))
    (hs : LSeriesSummable a s) :
    ∏' p : Primes, (1 - a p * (p : ℂ) ^ (-s) + c p * (p : ℂ) ^ (-2 * s))⁻¹ = LSeries a s :=
  (LSeries_eulerProduct_hasProd_of_recurrence h₁ hmul hrec hs).tprod_eq

end TauCeti
