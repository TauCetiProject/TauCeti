/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.EulerProduct.Basic
public import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Euler products of degree two

Mathlib's `EulerProduct.eulerProduct_hasProd` writes the Dirichlet series of a multiplicative
function as a product, over the primes, of the prime-power series `∑ₑ a(pᵉ) p^{-es}`. When the
prime-power coefficients obey a two-term linear recurrence

`a(p^{r+2}) = a(p) a(p^{r+1}) - d(p) a(p^r)`,

that local series is the reciprocal of a quadratic polynomial in `p^{-s}`:

`∑ₑ a(pᵉ) p^{-es} = (1 - a(p) p^{-s} + d(p) p^{-2s})⁻¹`.

This is the shape of the Euler product of a Hecke eigenform, where `d(p) = χ(p) p^{k-1}`, and
more generally of any `L`-function of degree two.

## Main results

* `TauCeti.tsum_mul_pow_eq_inv_of_recurrence`: a power series whose coefficients satisfy
  `b(r+2) = c b(r+1) - d b(r)`, `b(0) = 1` and `b(1) = c` sums, where it converges, to
  `(1 - c x + d x²)⁻¹`.
* `TauCeti.LSeries_eulerProduct_hasProd_of_recurrence`: the Euler product
  `L(a, s) = ∏ₚ (1 - a(p) p^{-s} + d(p) p^{-2s})⁻¹` for a multiplicative `a` with such a
  recurrence at every prime, wherever the Dirichlet series converges absolutely.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Theorem 5.9.2, whose proof runs through exactly this local computation.
-/

public section

open LSeries

namespace TauCeti

/-- **A power series with a two-term linear recurrence is the reciprocal of a quadratic.** If
`b 0 = 1`, `b 1 = c` and `b (r + 2) = c * b (r + 1) - d * b r` for every `r`, then wherever
`∑ b r * x ^ r` converges its sum is `(1 - c * x + d * x ^ 2)⁻¹`. In particular the quadratic
does not vanish there. -/
theorem tsum_mul_pow_eq_inv_of_recurrence {K : Type*} [Field K] [TopologicalSpace K]
    [IsTopologicalRing K] [T2Space K] {b : ℕ → K} {c d x : K} (h₀ : b 0 = 1) (h₁ : b 1 = c)
    (hrec : ∀ r, b (r + 2) = c * b (r + 1) - d * b r)
    (hsum : Summable fun r ↦ b r * x ^ r) :
    ∑' r, b r * x ^ r = (1 - c * x + d * x ^ 2)⁻¹ := by
  set S := ∑' r, b r * x ^ r with hS
  -- Peel off the first term, then the second: `S = 1 + c x + ∑ b (r + 2) x ^ (r + 2)`.
  have hsum₁ : Summable fun r ↦ b (r + 1) * x ^ (r + 1) :=
    (summable_nat_add_iff (f := fun r ↦ b r * x ^ r) 1).mpr hsum
  have hS₁ : S = 1 + ∑' r, b (r + 1) * x ^ (r + 1) := by
    rw [hS, hsum.tsum_eq_zero_add, h₀, pow_zero, mul_one]
  have hS₂ : ∑' r, b (r + 1) * x ^ (r + 1) = c * x + ∑' r, b (r + 2) * x ^ (r + 2) := by
    rw [hsum₁.tsum_eq_zero_add, h₁, zero_add, pow_one]
  -- The recurrence rewrites the tail through the two earlier series.
  have htail : ∑' r, b (r + 2) * x ^ (r + 2) =
      c * x * ∑' r, b (r + 1) * x ^ (r + 1) - d * x ^ 2 * S := by
    rw [hS, ← tsum_mul_left, ← tsum_mul_left, ← (hsum₁.mul_left _).tsum_sub (hsum.mul_left _)]
    exact tsum_congr fun r ↦ by rw [hrec]; ring
  have hmul : S * (1 - c * x + d * x ^ 2) = 1 := by
    linear_combination (1 - c * x) * hS₁ + hS₂ + htail
  exact eq_inv_of_mul_eq_one_left hmul

/-- **The Euler product of degree two.** Let `a : ℕ → ℂ` be multiplicative on coprime arguments
with `a 1 = 1`, and suppose that at every prime `p` its values on the powers of `p` satisfy the
recurrence `a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - d p * a (p ^ r)`. Wherever the Dirichlet
series of `a` converges absolutely,

`L(a, s) = ∏ₚ (1 - a(p) p^{-s} + d(p) p^{-2s})⁻¹`,

the product converging unconditionally over the primes. -/
theorem LSeries_eulerProduct_hasProd_of_recurrence {a d : ℕ → ℂ} (h₁ : a 1 = 1)
    (hmul : ∀ {m n : ℕ}, m.Coprime n → a (m * n) = a m * a n)
    (hrec : ∀ p : ℕ, p.Prime → ∀ r : ℕ,
      a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - d p * a (p ^ r))
    {s : ℂ} (hs : LSeriesSummable a s) :
    HasProd (fun p : Nat.Primes ↦
      (1 - a p * (p : ℂ) ^ (-s) + d p * (p : ℂ) ^ (-2 * s))⁻¹) (LSeries a s) := by
  have hterm_mul : ∀ {m n : ℕ}, m.Coprime n → term a s (m * n) = term a s m * term a s n := by
    intro m n hmn
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    rw [term_of_ne_zero (mul_ne_zero hm hn), term_of_ne_zero hm, term_of_ne_zero hn, hmul hmn,
      Nat.cast_mul, Complex.natCast_mul_natCast_cpow, mul_div_mul_comm]
  have hterm_one : term a s 1 = 1 := by
    rw [term_of_ne_zero one_ne_zero, h₁, Nat.cast_one, Complex.one_cpow, div_one]
  have hprod := EulerProduct.eulerProduct_hasProd hterm_one hterm_mul
    (summable_norm_iff.mpr hs) (term_zero a s)
  suffices hloc : ∀ p : Nat.Primes, ∑' e, term a s ((p : ℕ) ^ e) =
      (1 - a p * (p : ℂ) ^ (-s) + d p * (p : ℂ) ^ (-2 * s))⁻¹ by
    rw [funext hloc] at hprod
    exact hprod
  intro p
  -- The local factor at `p`: the prime-power terms are `a (p ^ e) * (p ^ (-s)) ^ e`.
  have hp := p.prop
  have hpow (e : ℕ) : term a s ((p : ℕ) ^ e) = a ((p : ℕ) ^ e) * ((p : ℂ) ^ (-s)) ^ e := by
    rw [term_of_ne_zero (pow_ne_zero _ hp.ne_zero), Nat.cast_pow,
      ← Complex.natCast_cpow_natCast_mul, ← Complex.cpow_nat_mul, mul_neg, Complex.cpow_neg,
      div_eq_mul_inv]
  have hsq : (p : ℂ) ^ (-2 * s) = ((p : ℂ) ^ (-s)) ^ 2 := by
    rw [← Complex.cpow_nat_mul, Nat.cast_ofNat, neg_mul, mul_neg]
  have hsum : Summable fun e ↦ a ((p : ℕ) ^ e) * ((p : ℂ) ^ (-s)) ^ e := by
    simpa only [Function.comp_def, hpow] using
      hs.comp_injective (Nat.pow_right_injective hp.two_le)
  rw [tsum_congr hpow, hsq]
  exact tsum_mul_pow_eq_inv_of_recurrence (b := fun e ↦ a ((p : ℕ) ^ e)) (by simpa using h₁)
    (by simp) (hrec p hp) hsum

end TauCeti
