/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import TauCeti.NumberTheory.LSeries.Convergence
import TauCeti.NumberTheory.LSeries.EulerProduct

/-!
# Dirichlet series of the form `ζ(s)^(k + 1) / ζ(2s)`

Let `a : ℕ → ℂ` be multiplicative on nonzero coprime arguments with `a 1 = 1`, and let its
L-series converge absolutely at `s` with `Re s > 1`. If at every prime `p` the sum of the
prime-power terms is `(1 + X) / (1 - X)^k`, where `X = p^(-s)`, then the L-series of `a` is
`ζ(s)^(k + 1) / ζ(2s)`. Indeed `(1 + X) / (1 - X)^k = (1 - X)^(-(k + 1)) (1 - X²)`, and the two
factors are the local factors of `ζ(s)^(k + 1)` and of `ζ(2s)⁻¹`; the Euler products of `a` and of
`riemannZeta` then match prime by prime.

This covers, among others, the squared divisor count (`k = 3`) and the divisor count of `n²`
(`k = 2`).

## Main results

* `TauCeti.LSeriesHasSum_riemannZeta_pow_div_riemannZeta_two_mul`: the comparison above.
* `TauCeti.riemannZeta_pow_eq_mul_of_LSeriesHasSum`: the multiplication form
  `ζ(s)^k = ζ(2s) L(a, s)` of an L-series with value `ζ(s)^k / ζ(2s)`.
-/

public section

namespace TauCeti

/-- A coefficient sequence, multiplicative on nonzero coprime arguments, whose L-series converges
absolutely and has local factor `(1 + X) / (1 - X)^k` at every prime, where `X = p^(-s)`, has
L-series `ζ(s)^(k + 1) / ζ(2s)`. -/
theorem LSeriesHasSum_riemannZeta_pow_div_riemannZeta_two_mul {a : ℕ → ℂ} {s : ℂ}
    (hs : 1 < s.re) (k : ℕ) (h₁ : a 1 = 1)
    (hmul : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → m.Coprime n → a (m * n) = a m * a n)
    (hsum : LSeriesSummable a s)
    (hlocal : ∀ p : Nat.Primes, ∑' e : ℕ, _root_.LSeries.term a s (p.val ^ e) =
      (1 + (p : ℂ) ^ (-s)) / (1 - (p : ℂ) ^ (-s)) ^ k) :
    LSeriesHasSum a s (riemannZeta s ^ (k + 1) / riemannZeta (2 * s)) := by
  have HP : HasProd (fun p : Nat.Primes ↦ ∑' e : ℕ, _root_.LSeries.term a s (p.val ^ e))
      (_root_.LSeries a s) :=
    EulerProduct.eulerProduct_hasProd (by simp [h₁])
      (TauCeti.LSeries.term_mul_of_coprime hmul) hsum.norm (_root_.LSeries.term_zero a s)
  have hs2 := one_lt_re_two_mul hs
  have hfactor (p : Nat.Primes) :
      (1 - (p : ℂ) ^ (-(2 * s)))⁻¹ * (∑' e : ℕ, _root_.LSeries.term a s (p.val ^ e)) =
        ((1 - (p : ℂ) ^ (-s))⁻¹) ^ (k + 1) := by
    rw [hlocal]
    have hexp : (p : ℂ) ^ (-(2 * s)) = ((p : ℂ) ^ (-s)) ^ 2 := by
      have hneg : -(2 * s) = -s + -s := by ring
      rw [hneg, Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr p.prop.ne_zero), pow_two]
    have h1 := Complex.one_sub_prime_cpow_ne_zero p.prop hs
    have h2 := Complex.one_sub_prime_cpow_ne_zero p.prop hs2
    have hsq : 1 - (p : ℂ) ^ (-(2 * s)) = (1 - (p : ℂ) ^ (-s)) * (1 + (p : ℂ) ^ (-s)) := by
      rw [hexp]
      ring
    have h3 : 1 + (p : ℂ) ^ (-s) ≠ 0 := right_ne_zero_of_mul (hsq ▸ h2)
    rw [hsq, mul_inv, div_eq_mul_inv, inv_pow, pow_succ']
    field_simp
  have H : HasProd (fun p : Nat.Primes ↦ ((1 - (p : ℂ) ^ (-s))⁻¹) ^ (k + 1))
      (riemannZeta (2 * s) * _root_.LSeries a s) := by
    simpa only [hfactor] using (riemannZeta_eulerProduct_hasProd hs2).mul HP
  have heq : _root_.LSeries a s = riemannZeta s ^ (k + 1) / riemannZeta (2 * s) :=
    (eq_div_iff (riemannZeta_ne_zero_of_one_lt_re hs2)).mpr (by
      simpa only [mul_comm] using H.unique ((riemannZeta_eulerProduct_hasProd hs).pow (k + 1)))
  exact heq ▸ hsum.LSeriesHasSum

/-- The multiplication form `ζ(s)^k = ζ(2s) L(a,s)` of an L-series with value
`ζ(s)^k / ζ(2s)`. -/
theorem riemannZeta_pow_eq_mul_of_LSeriesHasSum {a : ℕ → ℂ} {s : ℂ} (hs : 1 < s.re)
    {k : ℕ} (h : LSeriesHasSum a s (riemannZeta s ^ k / riemannZeta (2 * s))) :
    riemannZeta s ^ k = riemannZeta (2 * s) * _root_.LSeries a s := by
  simpa only [mul_comm] using ((eq_div_iff (riemannZeta_ne_zero_of_one_lt_re
    (one_lt_re_two_mul hs))).mp h.LSeries_eq).symm

end TauCeti
