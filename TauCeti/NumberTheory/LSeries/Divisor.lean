/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import TauCeti.NumberTheory.ArithmeticFunction.DivisorBounds
import TauCeti.NumberTheory.LSeries.EulerProduct

/-!
# The Dirichlet series of the squared divisor count

On `Re s > 1`, the squared number of divisors has an absolutely convergent Dirichlet series
with value `ζ(s)^4 / ζ(2s)`. The coefficient is zero at index zero, because `Nat.divisors 0` is
empty. The quotient-form `LSeriesHasSum` endpoint and the multiplication-form identity are both
provided. The proof uses the native subpower bound for divisor counts, multiplicativity, and
Mathlib's geometric-series moment formulas.

The statement corresponds to `zeta_pow_four_eq` in the PNT+ development. Here the proof
computes the specialized Euler factors directly, without introducing general complex divisor sums.

## References

* Alex Kontorovich, Terence Tao and contributors, [Prime Number Theorem and More][PNTDivisorSquare],
  `IwaniecKowalskiCh1.lean`, `zeta_pow_four_eq`.

[PNTDivisorSquare]: https://github.com/TauCetiProject/PrimeNumberTheoremAnd/blob/a90b1493fe9af9011c800856033c1ba7ac5fcc84/PrimeNumberTheoremAnd/IwaniecKowalskiCh1.lean
-/

public section

namespace TauCeti

private theorem divisor_sq_summable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n : ℕ ↦ (n.divisors.card : ℂ) ^ 2) s := by
  let ε : ℝ := (s.re - 1) / 4
  obtain ⟨C, _, hbound⟩ := exists_pos_card_divisors_le_rpow
    (show 0 < ε by dsimp [ε]; linarith)
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

private theorem hasSum_succ_sq_mul_geometric {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun k : ℕ ↦ ((k : ℂ) + 1) ^ 2 * x ^ k) ((1 + x) / (1 - x) ^ 3) := by
  have H := ((hasSum_sq_mul_geometric_of_norm_lt_one hx).add
    ((hasSum_coe_mul_geometric_of_norm_lt_one hx).mul_left 2)).add
    (hasSum_geometric_of_norm_lt_one hx)
  convert H using 1
  · ext k
    ring
  · have hne : 1 - x ≠ 0 := sub_ne_zero.mpr (fun h ↦ by
      have : x = 1 := h.symm
      simp only [this, norm_one, lt_self_iff_false] at hx)
    field_simp
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
  simpa only [hterm] using (hasSum_succ_sq_mul_geometric hx).tsum_eq

/-- The squared divisor count has Dirichlet series `ζ(s)^4 / ζ(2s)` on `Re s > 1`,
including absolute convergence. -/
theorem LSeriesHasSum_card_divisors_sq {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n : ℕ ↦ (n.divisors.card : ℂ) ^ 2) s
      (riemannZeta s ^ 4 / riemannZeta (2 * s)) := by
  let a : ℕ → ℂ := fun n ↦ (n.divisors.card : ℂ) ^ 2
  have hsum : LSeriesSummable a s := divisor_sq_summable hs
  have hmul : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → m.Coprime n →
      a (m * n) = a m * a n := by
    intro m n _ _ hmn
    simp only [a, hmn.card_divisors_mul, Nat.cast_mul, mul_pow]
  have HP : HasProd (fun p : Nat.Primes ↦ ∑' k : ℕ, _root_.LSeries.term a s (p.val ^ k))
      (_root_.LSeries a s) :=
    EulerProduct.eulerProduct_hasProd (by simp [a])
      (TauCeti.LSeries.term_mul_of_coprime hmul) hsum.norm (_root_.LSeries.term_zero a s)
  have hs2 : 1 < (2 * s).re := by
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    linarith
  have hfactor (p : Nat.Primes) :
      (1 - (p : ℂ) ^ (-(2 * s)))⁻¹ * (∑' k : ℕ, _root_.LSeries.term a s (p.val ^ k)) =
        ((1 - (p : ℂ) ^ (-s))⁻¹) ^ 4 := by
    rw [divisor_sq_local hs]
    have hexp : (p : ℂ) ^ (-(2 * s)) = ((p : ℂ) ^ (-s)) ^ 2 := by
      rw [show -(2 * s) = -s + -s by ring,
        Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr p.prop.ne_zero), pow_two]
    have h1 := Complex.one_sub_prime_cpow_ne_zero p.prop hs
    have h2 := Complex.one_sub_prime_cpow_ne_zero p.prop hs2
    rw [hexp] at h2 ⊢
    field_simp
    ring
  have H : HasProd (fun p : Nat.Primes ↦ ((1 - (p : ℂ) ^ (-s))⁻¹) ^ 4)
      (riemannZeta (2 * s) * _root_.LSeries a s) := by
    simpa only [hfactor] using (riemannZeta_eulerProduct_hasProd hs2).mul HP
  have heq : _root_.LSeries a s = riemannZeta s ^ 4 / riemannZeta (2 * s) :=
    (eq_div_iff (riemannZeta_ne_zero_of_one_lt_re hs2)).mpr
      (by simpa only [mul_comm] using H.unique ((riemannZeta_eulerProduct_hasProd hs).pow 4))
  exact heq ▸ hsum.LSeriesHasSum

/-- The divisor-square Euler identity `ζ(s)^4 = ζ(2s) L(τ²,s)` on `Re s > 1`. -/
theorem riemannZeta_pow_four_eq_mul_LSeries_divisor_sq {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s ^ 4 = riemannZeta (2 * s) *
      _root_.LSeries (fun n : ℕ ↦ (n.divisors.card : ℂ) ^ 2) s := by
  have h := LSeriesHasSum_card_divisors_sq hs
  have hs2 : 1 < (2 * s).re := by
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    linarith
  simpa only [mul_comm] using
    ((eq_div_iff (riemannZeta_ne_zero_of_one_lt_re hs2)).mp h.LSeries_eq).symm

end TauCeti
