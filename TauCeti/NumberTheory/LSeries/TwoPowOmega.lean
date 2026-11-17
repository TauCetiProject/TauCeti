/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk, The PrimeNumberTheoremAnd contributors, The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import TauCeti.NumberTheory.LSeries.EulerProduct

/-!
# The Dirichlet series of two to the number of distinct prime factors

The raw coefficients `2 ^ cardDistinctFactors n` have value one at zero, which the Dirichlet
series ignores. The series converges absolutely exactly on `Re s > 1`, has local Euler factor
`(1 + p ^ (-s)) / (1 - p ^ (-s))`, and equals `ζ(s)² / ζ(2s)` on that half-plane.

The argument is adapted from the distinct-prime-factor series in
[Arend Mellendijk and the PNT+ contributors, Prime Number Theorem and More][PNT].

[PNT]: https://github.com/TauCetiProject/PrimeNumberTheoremAnd/blob/05076dfe4e396e6dbdea50fde395a5154341f59e/PrimeNumberTheoremAnd/IwaniecKowalskiCh1.lean#L1084-L1337
-/

public section

open ArithmeticFunction Nat Complex
open scoped ArithmeticFunction.omega ArithmeticFunction.sigma ArithmeticFunction.zeta
open scoped LSeries.notation

namespace TauCeti

/-- The `2^ω` series converges absolutely exactly on the half-plane `Re s > 1`. -/
theorem LSeriesSummable_two_pow_cardDistinctFactors_iff {s : ℂ} :
    LSeriesSummable (fun n ↦ (2 : ℂ) ^ ω n) s ↔ 1 < s.re := by
  constructor
  · intro h
    by_contra hs
    have h1 : LSeriesSummable (fun n ↦ (2 : ℂ) ^ ω n) 1 :=
      h.of_re_le_re (by simpa using le_of_not_gt hs)
    have hone : LSeriesSummable (fun _ ↦ (1 : ℂ)) 1 := by
      apply Summable.of_norm_bounded h1.norm
      intro n
      apply _root_.LSeries.norm_term_le
      simpa using (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) :
        (1 : ℝ) ≤ 2 ^ ω n)
    exact (not_lt_of_ge (by norm_num : (1 : ℝ) ≤ 1)) (LSeriesSummable_one_iff.mp hone)
  · intro hs
    have hz : LSeriesSummable (↗(ζ : ArithmeticFunction ℂ)) s :=
      LSeriesSummable_zeta_iff.mpr hs
    have heq : (ζ : ArithmeticFunction ℕ) * ζ = σ 0 := by
      simpa only [pow_zero_eq_zeta] using (zeta_mul_pow_eq_sigma (k := 0))
    have ht : LSeriesSummable (fun n ↦ ((σ 0 n : ℕ) : ℂ)) s := by
      convert LSeriesSummable_mul hz hz using 1
      funext n
      rw [← natCoe_mul, heq]
      simp only [natCoe_apply]
    apply Summable.of_norm_bounded ht.norm
    intro n
    by_cases hn : n = 0
    · simp [hn]
    apply _root_.LSeries.norm_term_le
    simp only [norm_pow, norm_ofNat, Complex.norm_natCast]
    have hNat : 2 ^ ω n ≤ σ 0 n := by
      rw [cardDistinctFactors_eq_card_primeFactors, sigma_zero_apply,
        Nat.card_divisors hn, ← Finset.prod_const]
      apply Finset.prod_le_prod
      intro p hp
      exact Nat.succ_le_succ
        ((Nat.Prime.dvd_iff_one_le_factorization (prime_of_mem_primeFactors hp) hn).mp
          (dvd_of_mem_primeFactors hp))
    exact_mod_cast hNat

/-- The abscissa of absolute convergence of the `2^ω` series is one. -/
theorem abscissaOfAbsConv_two_pow_cardDistinctFactors :
    _root_.LSeries.abscissaOfAbsConv (fun n ↦ (2 : ℂ) ^ ω n) = 1 := by
  apply le_antisymm
  · apply _root_.LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    intro x hx
    exact LSeriesSummable_two_pow_cardDistinctFactors_iff.mpr hx
  · by_contra h
    have hs := LSeriesSummable_of_abscissaOfAbsConv_lt_re (s := (1 : ℂ))
      (by simpa using lt_of_not_ge h)
    exact (not_lt_of_ge (by norm_num : (1 : ℝ) ≤ 1))
      (LSeriesSummable_two_pow_cardDistinctFactors_iff.mp hs)

/-- The prime-power sum has local factor `(1 + p^(-s))/(1 - p^(-s))` for `Re s > 0`. -/
theorem tsum_term_prime_pow_two_pow_cardDistinctFactors {s : ℂ} {p : Nat.Primes}
    (hs : 0 < s.re) :
    (∑' e : ℕ, _root_.LSeries.term (fun n ↦ (2 : ℂ) ^ ω n) s (p.val ^ e)) =
      (1 + (p : ℂ) ^ (-s)) / (1 - (p : ℂ) ^ (-s)) := by
  have hq : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_natCast_cpow_of_pos p.prop.pos, neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.prop.one_lt) (neg_neg_of_pos hs)
  have hsum : HasSum (fun e : ℕ ↦
      _root_.LSeries.term (fun n ↦ (2 : ℂ) ^ ω n) s (p.val ^ e))
      (2 * (1 - (p : ℂ) ^ (-s))⁻¹ - 1) := by
    convert ((hasSum_geometric_of_norm_lt_one hq).mul_left (2 : ℂ)).sub
      (hasSum_ite_eq (0 : ℕ) (1 : ℂ)) using 1
    ext e
    rw [TauCeti.LSeries.term_pow p p.prop.ne_zero]
    cases e with
    | zero => norm_num
    | succ e =>
      rw [cardDistinctFactors_apply_prime_pow p.prop (Nat.succ_ne_zero e)]
      simp
  rw [hsum.tsum_eq]
  have hne : 1 - (p : ℂ) ^ (-s) ≠ 0 := by
    intro h
    have heq : (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
    simp [heq] at hq
  field_simp
  ring

/-- The Euler product for the `2^ω` series on its half-plane of absolute convergence. -/
theorem LSeries_two_pow_cardDistinctFactors_eulerProduct_hasProd {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes ↦
      (1 + (p : ℂ) ^ (-s)) / (1 - (p : ℂ) ^ (-s)))
      (_root_.LSeries (fun n ↦ (2 : ℂ) ^ ω n) s) := by
  have hmul : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → m.Coprime n →
      (2 : ℂ) ^ ω (m * n) = (2 : ℂ) ^ ω m * (2 : ℂ) ^ ω n := by
    intro m n _ _ hmn
    rw [cardDistinctFactors_mul hmn, pow_add]
  have H := EulerProduct.eulerProduct_hasProd (by simp)
    (TauCeti.LSeries.term_mul_of_coprime hmul)
    (LSeriesSummable_two_pow_cardDistinctFactors_iff.mpr hs).norm
    (_root_.LSeries.term_zero (fun n ↦ (2 : ℂ) ^ ω n) s)
  simpa only [_root_.LSeries,
    tsum_term_prime_pow_two_pow_cardDistinctFactors (lt_trans zero_lt_one hs)] using H

/-- The `2^ω` series gives the zeta correction `ζ(s)² = ζ(2s) L(2^ω,s)`. -/
theorem riemannZeta_sq_eq_mul_LSeries_two_pow_cardDistinctFactors {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s ^ 2 = riemannZeta (2 * s) *
      _root_.LSeries (fun n ↦ (2 : ℂ) ^ ω n) s := by
  have hs2 : 1 < (2 * s).re := by
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    linarith
  have hfactor (p : Nat.Primes) :
      (1 - (p : ℂ) ^ (-(2 * s)))⁻¹ *
          ((1 + (p : ℂ) ^ (-s)) / (1 - (p : ℂ) ^ (-s))) =
        (1 - (p : ℂ) ^ (-s))⁻¹ * (1 - (p : ℂ) ^ (-s))⁻¹ := by
    have hexp : (p : ℂ) ^ (-(2 * s)) = ((p : ℂ) ^ (-s)) ^ 2 := by
      have hneg : -(2 * s) = -s + -s := by ring
      rw [hneg, Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr p.prop.ne_zero), pow_two]
    have h1 := Complex.one_sub_prime_cpow_ne_zero p.prop hs
    have h2 := Complex.one_sub_prime_cpow_ne_zero p.prop hs2
    rw [hexp] at h2 ⊢
    field_simp
    ring
  have H := (riemannZeta_eulerProduct_hasProd hs2).mul
    (LSeries_two_pow_cardDistinctFactors_eulerProduct_hasProd hs)
  have H' : HasProd (fun p : Nat.Primes ↦
      (1 - (p : ℂ) ^ (-s))⁻¹ * (1 - (p : ℂ) ^ (-s))⁻¹)
      (riemannZeta (2 * s) * _root_.LSeries (fun n ↦ (2 : ℂ) ^ ω n) s) := by
    simpa only [hfactor] using H
  simpa only [pow_two] using
    ((riemannZeta_eulerProduct_hasProd hs).mul (riemannZeta_eulerProduct_hasProd hs)).unique H'

/-- The `2^ω` Dirichlet terms have sum `ζ(s)² / ζ(2s)` on `Re s > 1`. -/
theorem LSeriesHasSum_two_pow_cardDistinctFactors {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n ↦ (2 : ℂ) ^ ω n) s (riemannZeta s ^ 2 / riemannZeta (2 * s)) := by
  have hs2 : 1 < (2 * s).re := by
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    linarith
  have heq : _root_.LSeries (fun n ↦ (2 : ℂ) ^ ω n) s =
      riemannZeta s ^ 2 / riemannZeta (2 * s) := by
    apply (eq_div_iff (riemannZeta_ne_zero_of_one_lt_re hs2)).mpr
    simpa only [mul_comm] using (riemannZeta_sq_eq_mul_LSeries_two_pow_cardDistinctFactors hs).symm
  exact heq ▸ (LSeriesSummable_two_pow_cardDistinctFactors_iff.mpr hs).LSeriesHasSum

end TauCeti
