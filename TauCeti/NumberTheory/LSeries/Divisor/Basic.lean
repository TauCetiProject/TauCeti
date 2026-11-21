/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import TauCeti.Analysis.SpecificLimits.Normed
import TauCeti.NumberTheory.ArithmeticFunction.DivisorBounds
import TauCeti.NumberTheory.LSeries.EulerProduct
import TauCeti.NumberTheory.LSeries.RiemannZeta.EulerProduct

/-!
# Dirichlet series of divisor counts with a `ζ(2s)` correction

On `Re s > 1`, the squared number of divisors has an absolutely convergent Dirichlet series
with value `ζ(s)^4 / ζ(2s)`. The coefficient is zero at index zero, because `Nat.divisors 0` is
empty. The quotient-form `LSeriesHasSum` endpoint and the multiplication-form identity are both
provided. The factor `ζ(2s)` is the Euler correction relating the squared divisor counts to
the fourth power of the Riemann zeta function: at each prime, the divisor-square series has
local factor `(1 + X) / (1 - X)³`, rather than the factor `(1 - X)⁻⁴` of `ζ(s)⁴`.

Likewise the divisor count `τ(n²)` of `n²` has an absolutely convergent Dirichlet series
with value `ζ(s)^3 / ζ(2s)` on `Re s > 1`: since `τ(p^(2k)) = 2k + 1`, its local factor is
`(1 + X) / (1 - X)² = (1 - X)⁻³ (1 - X²)`.

Both series are instances of the Euler-product comparison
`TauCeti.LSeriesHasSum_riemannZeta_pow_div_riemannZeta_two_mul`.

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

/-- The squared divisor count has Dirichlet series `ζ(s)^4 / ζ(2s)` on `Re s > 1`,
including absolute convergence. -/
theorem LSeriesHasSum_card_divisors_sq {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n : ℕ ↦ (n.divisors.card : ℂ) ^ 2) s
      (riemannZeta s ^ 4 / riemannZeta (2 * s)) := by
  refine LSeriesHasSum_riemannZeta_pow_div_riemannZeta_two_mul hs 3 (by simp)
    (fun {m n} _ _ hmn ↦ ?_) (divisor_sq_summable hs) (divisor_sq_local hs)
  simp only [hmn.card_divisors_mul, Nat.cast_mul, mul_pow]

/-- The divisor-square Euler identity `ζ(s)^4 = ζ(2s) L(τ²,s)` on `Re s > 1`. -/
theorem riemannZeta_pow_four_eq_mul_LSeries_divisor_sq {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s ^ 4 = riemannZeta (2 * s) *
      _root_.LSeries (fun n : ℕ ↦ (n.divisors.card : ℂ) ^ 2) s :=
  riemannZeta_pow_eq_mul_of_LSeriesHasSum hs (LSeriesHasSum_card_divisors_sq hs)

private theorem card_divisors_comp_sq_summable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n : ℕ ↦ ((n ^ 2).divisors.card : ℂ)) s := by
  let ε : ℝ := (s.re - 1) / 4
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨C, _, hbound⟩ := exists_pos_card_divisors_le_rpow hε
  apply LSeriesSummable_of_le_const_mul_rpow (x := 1 + 2 * ε)
    (by dsimp [ε]; linarith)
  refine ⟨C, fun n _hn ↦ ?_⟩
  rw [Complex.norm_natCast]
  calc
    ((n ^ 2).divisors.card : ℝ) ≤ C * ((n ^ 2 : ℕ) : ℝ) ^ ε := hbound (n ^ 2)
    _ = C * (n : ℝ) ^ (1 + 2 * ε - 1) := by
      rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
      congr 2
      push_cast
      ring

private theorem card_divisors_comp_sq_local {s : ℂ} (hs : 1 < s.re) (p : Nat.Primes) :
    (∑' k : ℕ, _root_.LSeries.term (fun n : ℕ ↦ ((n ^ 2).divisors.card : ℂ)) s
      (p.val ^ k)) = (1 + (p : ℂ) ^ (-s)) / (1 - (p : ℂ) ^ (-s)) ^ 2 := by
  have hx : ‖(p : ℂ) ^ (-s)‖ < 1 :=
    (Complex.norm_prime_cpow_le_one_half p hs).trans_lt (by norm_num)
  have hterm (k : ℕ) :
      _root_.LSeries.term (fun n : ℕ ↦ ((n ^ 2).divisors.card : ℂ)) s (p.val ^ k) =
        (2 * (k : ℂ) + 1) * ((p : ℂ) ^ (-s)) ^ k := by
    rw [TauCeti.LSeries.term_pow p p.prop.ne_zero k, ← pow_mul,
      ← ArithmeticFunction.sigma_zero_apply,
      ArithmeticFunction.sigma_zero_apply_prime_pow p.prop]
    push_cast
    ring
  simp only [hterm, (hasSum_affine_mul_geometric_of_norm_lt_one hx 2 1).tsum_eq]
  norm_num

/-- The divisor count `τ(n²)` of `n²` has Dirichlet series `ζ(s)^3 / ζ(2s)` on `Re s > 1`,
including absolute convergence. -/
theorem LSeriesHasSum_card_divisors_comp_sq {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n : ℕ ↦ ((n ^ 2).divisors.card : ℂ)) s
      (riemannZeta s ^ 3 / riemannZeta (2 * s)) := by
  refine LSeriesHasSum_riemannZeta_pow_div_riemannZeta_two_mul hs 2 (by simp)
    (fun {m n} _ _ hmn ↦ ?_) (card_divisors_comp_sq_summable hs) (card_divisors_comp_sq_local hs)
  simp only [mul_pow, (hmn.pow 2 2).card_divisors_mul, Nat.cast_mul]

/-- The Euler identity `ζ(s)^3 = ζ(2s) L(τ(n²),s)` on `Re s > 1`. -/
theorem riemannZeta_pow_three_eq_mul_LSeries_card_divisors_comp_sq {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s ^ 3 = riemannZeta (2 * s) *
      _root_.LSeries (fun n : ℕ ↦ ((n ^ 2).divisors.card : ℂ)) s :=
  riemannZeta_pow_eq_mul_of_LSeriesHasSum hs (LSeriesHasSum_card_divisors_comp_sq hs)

end TauCeti
