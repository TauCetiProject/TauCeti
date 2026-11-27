/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk, The PrimeNumberTheoremAnd contributors, The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
public import TauCeti.NumberTheory.LSeries.Moebius
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Dirichlet
import TauCeti.NumberTheory.ArithmeticFunction.Moebius
import TauCeti.NumberTheory.LSeries.Convergence
import TauCeti.NumberTheory.LSeries.EulerProduct

/-!
# The Dirichlet series of two to the number of distinct prime factors

The raw coefficients `2 ^ cardDistinctFactors n` have value one at zero, which the Dirichlet
series ignores. The series converges absolutely exactly on `Re s > 1`, has local Euler factor
`(1 + p ^ (-s)) / (1 - p ^ (-s))`, and equals `ζ(s)² / ζ(2s)` on that half-plane.

Off index zero the coefficients count the squarefree divisors, `2 ^ ω = μ² ⍟ 1`, so the series is
the product of `ζ(s)` with the series `ζ(s) / ζ(2s)` of `μ²`; this gives convergence and the sum.
Since `2 ^ ω(n) ≥ 1`, the series dominates that of the constant sequence `1`, which fixes its
abscissa of absolute convergence at `1`.

The Euler product argument is adapted from the distinct-prime-factor series in
[Arend Mellendijk and the PNT+ contributors, Prime Number Theorem and More][PNT].

[PNT]: https://github.com/TauCetiProject/PrimeNumberTheoremAnd/blob/05076dfe4e396e6dbdea50fde395a5154341f59e/PrimeNumberTheoremAnd/IwaniecKowalskiCh1.lean#L1084-L1337
-/

public section

open ArithmeticFunction Nat Complex
open scoped ArithmeticFunction.omega ArithmeticFunction.sigma ArithmeticFunction.zeta
open scoped LSeries.notation

namespace TauCeti

/-- Off index zero, the coefficients `2 ^ ω(n)` are the Dirichlet convolution of `μ²` with the
constant sequence `1`. -/
private theorem moebius_sq_convolution_one_apply {n : ℕ} (hn : n ≠ 0) :
    ((fun n ↦ (moebius n : ℂ) ^ 2) ⍟ 1) n = (2 : ℂ) ^ ω n := by
  simp only [_root_.LSeries.convolution_def, Pi.one_apply, mul_one]
  rw [Nat.sum_divisorsAntidiagonal (fun a _ ↦ (moebius a : ℂ) ^ 2), sum_divisors_moebius_sq hn]

/-- The `2^ω` series converges absolutely exactly on the half-plane `Re s > 1`. -/
theorem LSeriesSummable_two_pow_cardDistinctFactors_iff {s : ℂ} :
    LSeriesSummable (fun n ↦ (2 : ℂ) ^ ω n) s ↔ 1 < s.re := by
  constructor
  · intro hf
    refine LSeriesSummable_one_iff.mp (Summable.of_norm_bounded hf.norm fun n ↦ ?_)
    refine _root_.LSeries.norm_term_le s ?_
    simpa using one_le_pow₀ (M₀ := ℝ) (n := ω n) one_le_two
  · intro hs
    refine (LSeriesSummable_congr s fun hn ↦ moebius_sq_convolution_one_apply hn).mp ?_
    exact (LSeriesSummable_moebius_sq_iff.mpr hs).convolution (LSeriesSummable_one_iff.mpr hs)

/-- The abscissa of absolute convergence of the `2^ω` series is one. -/
theorem abscissaOfAbsConv_two_pow_cardDistinctFactors :
    _root_.LSeries.abscissaOfAbsConv (fun n ↦ (2 : ℂ) ^ ω n) = 1 :=
  (LSeries.abscissaOfAbsConv_eq_of_LSeriesSummable_iff fun _ ↦
    LSeriesSummable_two_pow_cardDistinctFactors_iff).trans EReal.coe_one

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
  have hs2 := one_lt_re_two_mul hs
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

/-- The `2^ω` Dirichlet terms have sum `ζ(s)² / ζ(2s)` on `Re s > 1`: the series is the
product of the series `ζ(s) / ζ(2s)` of `μ²` with `ζ(s)`. -/
theorem LSeriesHasSum_two_pow_cardDistinctFactors {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n ↦ (2 : ℂ) ^ ω n) s (riemannZeta s ^ 2 / riemannZeta (2 * s)) := by
  have hs2 := one_lt_re_two_mul hs
  have hconv := ((LSeriesSummable_moebius_sq_iff.mpr hs).LSeriesHasSum).convolution
    (LSeriesHasSum_one hs)
  rw [LSeriesHasSum_congr s _ fun hn ↦ (moebius_sq_convolution_one_apply hn).symm]
  convert hconv using 1
  rw [div_eq_iff (riemannZeta_ne_zero_of_one_lt_re hs2), sq, mul_comm _ (riemannZeta (2 * s)),
    ← mul_assoc, ← riemannZeta_eq_mul_LSeries_moebius_sq hs]

end TauCeti
