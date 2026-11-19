/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.Moebius
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Dirichlet
import TauCeti.NumberTheory.ArithmeticFunction.Moebius
import TauCeti.NumberTheory.LSeries.Convergence

/-!
# The Dirichlet series of `2 ^ ω`

The coefficients `2 ^ ω(n)`, where `ω(n)` is the number of distinct prime factors of `n`, count
the squarefree divisors of `n ≠ 0`: `2 ^ ω = μ² ⍟ 1`. Their Dirichlet series therefore converges
absolutely exactly on `Re s > 1`, where its sum is `ζ(s)² / ζ(2s)`, the product of `ζ(s)` with the
series `ζ(s) / ζ(2s)` of `μ²`. Since `2 ^ ω(n) ≥ 1`, the series dominates that of the constant
sequence `1`, which fixes its abscissa of absolute convergence at `1`.

## Main results

* `TauCeti.LSeriesSummable_two_pow_cardDistinctFactors_iff`: absolute convergence exactly on
  `Re s > 1`.
* `TauCeti.abscissaOfAbsConv_two_pow_cardDistinctFactors`: the abscissa of absolute convergence
  is `1`.
* `TauCeti.LSeriesHasSum_two_pow_cardDistinctFactors`: the sum is `ζ(s)² / ζ(2s)` on `Re s > 1`.

## References

* G. H. Hardy and E. M. Wright, *An Introduction to the Theory of Numbers*, Chapter XVII,
  the generating functions of arithmetical functions.
-/

public section

open ArithmeticFunction
open scoped ArithmeticFunction.omega LSeries.notation

namespace TauCeti

/-- Off index zero, the coefficients `2 ^ ω(n)` are the Dirichlet convolution of `μ²` with the
constant sequence `1`. -/
private theorem moebius_sq_convolution_one_apply {n : ℕ} (hn : n ≠ 0) :
    ((fun n ↦ (moebius n : ℂ) ^ 2) ⍟ 1) n = (2 : ℂ) ^ ω n := by
  simp only [LSeries.convolution_def, Pi.one_apply, mul_one]
  rw [Nat.sum_divisorsAntidiagonal (fun a _ ↦ (moebius a : ℂ) ^ 2), sum_divisors_moebius_sq hn]

/-- The Dirichlet series of `2 ^ ω` converges absolutely exactly on `Re s > 1`. -/
theorem LSeriesSummable_two_pow_cardDistinctFactors_iff {s : ℂ} :
    LSeriesSummable (fun n ↦ (2 : ℂ) ^ ω n) s ↔ 1 < s.re := by
  constructor
  · intro hf
    refine LSeriesSummable_one_iff.mp (Summable.of_norm_bounded hf.norm fun n ↦ ?_)
    refine LSeries.norm_term_le s ?_
    simpa using one_le_pow₀ (M₀ := ℝ) (n := ω n) one_le_two
  · intro hs
    refine (LSeriesSummable_congr s fun hn ↦ moebius_sq_convolution_one_apply hn).mp ?_
    exact (LSeriesSummable_moebius_sq_iff.mpr hs).convolution (LSeriesSummable_one_iff.mpr hs)

/-- The abscissa of absolute convergence of the Dirichlet series of `2 ^ ω` is one. -/
theorem abscissaOfAbsConv_two_pow_cardDistinctFactors :
    LSeries.abscissaOfAbsConv (fun n ↦ (2 : ℂ) ^ ω n) = 1 :=
  (LSeries.abscissaOfAbsConv_eq_of_LSeriesSummable_iff fun _ ↦
    LSeriesSummable_two_pow_cardDistinctFactors_iff).trans EReal.coe_one

/-- On `Re s > 1` the Dirichlet series of `2 ^ ω` has sum `ζ(s)² / ζ(2s)`. -/
theorem LSeriesHasSum_two_pow_cardDistinctFactors {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n ↦ (2 : ℂ) ^ ω n) s (riemannZeta s ^ 2 / riemannZeta (2 * s)) := by
  have hs2 : 1 < (2 * s).re := by
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    linarith
  have hconv := ((LSeriesSummable_moebius_sq_iff.mpr hs).LSeriesHasSum).convolution
    (LSeriesHasSum_one hs)
  rw [LSeriesHasSum_congr s _ fun hn ↦ (moebius_sq_convolution_one_apply hn).symm]
  convert hconv using 1
  rw [div_eq_iff (riemannZeta_ne_zero_of_one_lt_re hs2), sq, mul_comm _ (riemannZeta (2 * s)),
    ← mul_assoc, ← riemannZeta_eq_mul_LSeries_moebius_sq hs]

end TauCeti
