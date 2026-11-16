/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import TauCeti.Analysis.SpecificLimits.Normed
import TauCeti.NumberTheory.ArithmeticFunction.DivisorBounds
import TauCeti.NumberTheory.LSeries.EulerProduct

/-!
# Dirichlet series of divisor counts with a `ζ(2s)` correction

On `Re s > 1`, the squared number of divisors has an absolutely convergent Dirichlet series
with value `ζ(s)^4 / ζ(2s)`. The coefficient is zero at index zero, because `Nat.divisors 0` is
empty. The quotient-form `LSeriesHasSum` endpoint and the multiplication-form identity are both
provided. The factor `ζ(2s)` is the Euler correction relating the squared divisor counts to
the fourth power of the Riemann zeta function: at each prime, the divisor-square series has
local factor `(1 + X) / (1 - X)³`, rather than the factor `(1 - X)⁻⁴` of `ζ(s)⁴`.

Likewise the divisor count `τ(n²) = σ₀(n²)` of `n²` has an absolutely convergent Dirichlet series
with value `ζ(s)^3 / ζ(2s)` on `Re s > 1`: since `τ(p^(2k)) = 2k + 1`, its local factor is
`(1 + X) / (1 - X)² = (1 - X)⁻³ (1 - X²)`.

The statements correspond to `zeta_pow_four_eq` and `zeta_pow_three_eq` in the PNT+ development.

## References

* Alex Kontorovich, Terence Tao and contributors, [Prime Number Theorem and More][PNTDivisorSquare],
  `IwaniecKowalskiCh1.lean`, `zeta_pow_four_eq` and `zeta_pow_three_eq`.

[PNTDivisorSquare]: https://github.com/TauCetiProject/PrimeNumberTheoremAnd/blob/a90b1493fe9af9011c800856033c1ba7ac5fcc84/PrimeNumberTheoremAnd/IwaniecKowalskiCh1.lean
-/

public section

namespace TauCeti

private theorem divisor_sq_summable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n : ℕ ↦ (n.divisors.card : ℂ) ^ 2) s := by
  let ε : ℝ := (s.re - 1) / 4
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨C, _, hbound⟩ := exists_pos_card_divisors_le_rpow hε
  apply LSeriesSummable_of_le_const_mul_rpow (x := 1 + 2 * ε)
    (by dsimp [ε]; linarith)
  refine ⟨C ^ 2, fun n _hn ↦ ?_⟩
  rw [norm_pow, Complex.norm_natCast]
  calc
    (n.divisors.card : ℝ) ^ 2 ≤ (C * (n : ℝ) ^ ε) ^ 2 := by
      gcongr
      exact hbound n
    _ = C ^ 2 * (n : ℝ) ^ (1 + 2 * ε - 1) := by
      rw [mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg n)]
      congr 2
      ring

private theorem divisor_sq_local {s : ℂ} (hs : 1 < s.re) (p : Nat.Primes) :
    (∑' k : ℕ, _root_.LSeries.term (fun n : ℕ ↦ (n.divisors.card : ℂ) ^ 2) s
      (p.val ^ k)) = (1 + (p : ℂ) ^ (-s)) / (1 - (p : ℂ) ^ (-s)) ^ 3 := by
  have hx : ‖(p : ℂ) ^ (-s)‖ < 1 :=
    (Complex.norm_prime_cpow_le_one_half p hs).trans_lt (by norm_num)
  have hterm (k : ℕ) :
      _root_.LSeries.term (fun n : ℕ ↦ (n.divisors.card : ℂ) ^ 2) s (p.val ^ k) =
        ((k : ℂ) + 1) ^ 2 * ((p : ℂ) ^ (-s)) ^ k := by
    rw [TauCeti.LSeries.term_pow p p.prop.ne_zero k]
    rw [← ArithmeticFunction.sigma_zero_apply,
      ArithmeticFunction.sigma_zero_apply_prime_pow p.prop]
    push_cast
    rfl
  simpa only [hterm] using (hasSum_succ_sq_mul_geometric_of_norm_lt_one hx).tsum_eq

private theorem one_lt_re_two_mul {s : ℂ} (hs : 1 < s.re) : 1 < (2 * s).re := by
  simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
  linarith

/-- A coefficient sequence, multiplicative on nonzero coprime arguments, whose L-series converges
absolutely and has local factor `(1 + X) / (1 - X)^k` at every prime, where `X = p^(-s)`, has
L-series `ζ(s)^(k + 1) / ζ(2s)`. -/
private theorem LSeriesHasSum_of_local_factor {a : ℕ → ℂ} {s : ℂ} (hs : 1 < s.re) (k : ℕ)
    (h₁ : a 1 = 1) (hmul : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → m.Coprime n → a (m * n) = a m * a n)
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
private theorem riemannZeta_pow_eq_mul_of_LSeriesHasSum {a : ℕ → ℂ} {s : ℂ} (hs : 1 < s.re)
    {k : ℕ} (h : LSeriesHasSum a s (riemannZeta s ^ k / riemannZeta (2 * s))) :
    riemannZeta s ^ k = riemannZeta (2 * s) * _root_.LSeries a s := by
  simpa only [mul_comm] using ((eq_div_iff (riemannZeta_ne_zero_of_one_lt_re
    (one_lt_re_two_mul hs))).mp h.LSeries_eq).symm

/-- The squared divisor count has Dirichlet series `ζ(s)^4 / ζ(2s)` on `Re s > 1`,
including absolute convergence. -/
theorem LSeriesHasSum_card_divisors_sq {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n : ℕ ↦ (n.divisors.card : ℂ) ^ 2) s
      (riemannZeta s ^ 4 / riemannZeta (2 * s)) := by
  refine LSeriesHasSum_of_local_factor hs 3 (by simp) (fun {m n} _ _ hmn ↦ ?_)
    (divisor_sq_summable hs) (divisor_sq_local hs)
  simp only [hmn.card_divisors_mul, Nat.cast_mul, mul_pow]

/-- The divisor-square Euler identity `ζ(s)^4 = ζ(2s) L(τ²,s)` on `Re s > 1`. -/
theorem riemannZeta_pow_four_eq_mul_LSeries_divisor_sq {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s ^ 4 = riemannZeta (2 * s) *
      _root_.LSeries (fun n : ℕ ↦ (n.divisors.card : ℂ) ^ 2) s :=
  riemannZeta_pow_eq_mul_of_LSeriesHasSum hs (LSeriesHasSum_card_divisors_sq hs)

private theorem sigma_zero_sq_summable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n : ℕ ↦ (ArithmeticFunction.sigma 0 (n ^ 2) : ℂ)) s := by
  let ε : ℝ := (s.re - 1) / 4
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨C, _, hbound⟩ := exists_pos_card_divisors_le_rpow hε
  apply LSeriesSummable_of_le_const_mul_rpow (x := 1 + 2 * ε)
    (by dsimp [ε]; linarith)
  refine ⟨C, fun n _hn ↦ ?_⟩
  rw [Complex.norm_natCast, ArithmeticFunction.sigma_zero_apply]
  calc
    ((n ^ 2).divisors.card : ℝ) ≤ C * ((n ^ 2 : ℕ) : ℝ) ^ ε := hbound (n ^ 2)
    _ = C * (n : ℝ) ^ (1 + 2 * ε - 1) := by
      rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
      congr 2
      push_cast
      ring

private theorem sigma_zero_sq_local {s : ℂ} (hs : 1 < s.re) (p : Nat.Primes) :
    (∑' k : ℕ, _root_.LSeries.term (fun n : ℕ ↦ (ArithmeticFunction.sigma 0 (n ^ 2) : ℂ)) s
      (p.val ^ k)) = (1 + (p : ℂ) ^ (-s)) / (1 - (p : ℂ) ^ (-s)) ^ 2 := by
  have hx : ‖(p : ℂ) ^ (-s)‖ < 1 :=
    (Complex.norm_prime_cpow_le_one_half p hs).trans_lt (by norm_num)
  have hterm (k : ℕ) :
      _root_.LSeries.term (fun n : ℕ ↦ (ArithmeticFunction.sigma 0 (n ^ 2) : ℂ)) s
        (p.val ^ k) = (2 * (k : ℂ) + 1) * ((p : ℂ) ^ (-s)) ^ k := by
    rw [TauCeti.LSeries.term_pow p p.prop.ne_zero k, ← pow_mul,
      ArithmeticFunction.sigma_zero_apply_prime_pow p.prop]
    push_cast
    ring
  simpa only [hterm] using (hasSum_two_mul_add_one_mul_geometric_of_norm_lt_one hx).tsum_eq

/-- The divisor count of `n²` has Dirichlet series `ζ(s)^3 / ζ(2s)` on `Re s > 1`,
including absolute convergence. -/
theorem LSeriesHasSum_sigma_zero_sq {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n : ℕ ↦ (ArithmeticFunction.sigma 0 (n ^ 2) : ℂ)) s
      (riemannZeta s ^ 3 / riemannZeta (2 * s)) := by
  refine LSeriesHasSum_of_local_factor hs 2 (by simp) (fun {m n} _ _ hmn ↦ ?_)
    (sigma_zero_sq_summable hs) (sigma_zero_sq_local hs)
  simp only [mul_pow,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (hmn.pow 2 2), Nat.cast_mul]

/-- The Euler identity `ζ(s)^3 = ζ(2s) L(τ(n²),s)` on `Re s > 1`. -/
theorem riemannZeta_pow_three_eq_mul_LSeries_sigma_zero_sq {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s ^ 3 = riemannZeta (2 * s) *
      _root_.LSeries (fun n : ℕ ↦ (ArithmeticFunction.sigma 0 (n ^ 2) : ℂ)) s :=
  riemannZeta_pow_eq_mul_of_LSeriesHasSum hs (LSeriesHasSum_sigma_zero_sq hs)

end TauCeti
