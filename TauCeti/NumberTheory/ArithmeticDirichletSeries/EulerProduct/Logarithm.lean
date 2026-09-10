/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Complex.LogBounds
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Analytic

import Mathlib.NumberTheory.EulerProduct.ExpLog

/-!
# The Euler product over the primes of a number field, in exponential form

Mathlib's `EulerProduct.exp_tsum_primes_log_eq_tsum` writes the Euler product of a completely
multiplicative `f : ℕ →*₀ ℂ` as `exp (∑' p, -log (1 - f p))`. This file is the ideal-indexed
analogue, over the height-one primes of the ring of integers of a number field, mirroring the way
`TauCeti.MultiplicativeIdealWeight.hasProd_eulerFactor` mirrors Mathlib's product form.

The logarithm is taken factor by factor, using the principal value: absolute convergence of the
ideal-indexed series forces each local ratio into the open unit disc, where `Complex.log (1 - ·)`
is defined without choosing anything.

**What this does not give.** `exp` is not injective, so an identity of the form `exp t = L`
determines `t` only modulo `2πi ℤ`; these theorems therefore do not exhibit a logarithm *of* the
`L`-series, and in particular are not a holomorphic branch on a region.
`TauCeti.MultiplicativeIdealWeight.LSeries_ne_zero_of_summable_idealTerm` supplies nonvanishing
pointwise, wherever the ideal-indexed series converges absolutely; a branch needs more than that —
a simply connected zero-free region on which to choose one — and is not constructed here.

## Main results

* `TauCeti.MultiplicativeIdealWeight.exp_tsum_neg_log_one_sub_eq_LSeries`: the `L`-series as the
  exponential of a sum of principal logarithms over the primes.
* `TauCeti.MultiplicativeIdealWeight.tsum_prime_pow_eq_tsum_neg_log_one_sub`: that sum re-indexed
  by a prime and an exponent, as an identity of complex numbers.
* `TauCeti.MultiplicativeIdealWeight.exp_tsum_prime_pow_eq_LSeries`: the exponential form of the
  re-indexed sum.
-/

public section

namespace TauCeti

open Complex IsDedekindDomain

open scoped NumberField

namespace MultiplicativeIdealWeight

open IdealArithmeticFunction

variable {K : Type*} [Field K] [NumberField K] (χ : MultiplicativeIdealWeight K) {s : ℂ}

/-- **The Euler product in exponential form.** For a completely multiplicative ideal weight whose
ideal-indexed series converges absolutely at `s`, the `L`-series is the exponential of the sum of
principal logarithms `-log (1 - χ(P) N(P)⁻ˢ)` over the height-one primes.

The sum is not thereby a logarithm of the `L`-series: `exp` identifies it only modulo `2πi ℤ`.
This is the number-field analogue of Mathlib's `EulerProduct.exp_tsum_primes_log_eq_tsum`, and
carries the same limitation. -/
theorem exp_tsum_neg_log_one_sub_eq_LSeries
    (hs : Summable (idealTerm K χ.toIdealArithmeticFunction s)) :
    exp (∑' P : HeightOneSpectrum (𝓞 K),
        -log (1 - χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s)) =
      LSeries (normCoeff K χ.toIdealArithmeticFunction) s := by
  have hne := χ.one_sub_div_ne_zero_of_summable_idealTerm hs
  have H := (Summable.clog_one_sub
    (χ.summable_div_of_summable_idealTerm hs)).neg.hasSum.cexp.tprod_eq
  simp only [Function.comp_apply, exp_neg, exp_log (hne _)] at H
  exact H.symm.trans (χ.hasProd_eulerFactor hs).tprod_eq

/-- **The prime-power sum is the prime-indexed logarithm sum.**  Substituting the Taylor series of
`-log (1 - ·)` at each prime and regrouping over the primes identifies the two sums *as complex
numbers*, before any exponential is taken.  This is the statement a consumer needs in order to
rewrite one into the other; the exponential form below follows from it. -/
theorem tsum_prime_pow_eq_tsum_neg_log_one_sub
    (hs : Summable (idealTerm K χ.toIdealArithmeticFunction s)) :
    ∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
        (χ pe.1.asIdeal / (Ideal.absNorm pe.1.asIdeal : ℂ) ^ s) ^ (pe.2 + 1) / ((pe.2 : ℂ) + 1) =
      ∑' P : HeightOneSpectrum (𝓞 K),
        -log (1 - χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s) :=
  tsum_taylorSeries_neg_log
    (r := fun P : HeightOneSpectrum (𝓞 K) ↦ χ P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s)
    (χ.summable_div_of_summable_idealTerm hs) (χ.norm_div_lt_one_of_summable_idealTerm hs)

/-- **The Euler product expanded over prime powers.**  The `L`-series is the exponential of the
sum over pairs `(P, e)` of a prime and an exponent.  The caveat above applies unchanged: `exp` is
not injective, so this identifies the double sum only modulo `2πi ℤ` and does not exhibit a
logarithm of the `L`-series. -/
theorem exp_tsum_prime_pow_eq_LSeries
    (hs : Summable (idealTerm K χ.toIdealArithmeticFunction s)) :
    exp (∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
        (χ pe.1.asIdeal / (Ideal.absNorm pe.1.asIdeal : ℂ) ^ s) ^ (pe.2 + 1) / ((pe.2 : ℂ) + 1)) =
      LSeries (normCoeff K χ.toIdealArithmeticFunction) s := by
  rw [χ.tsum_prime_pow_eq_tsum_neg_log_one_sub hs, χ.exp_tsum_neg_log_one_sub_eq_LSeries hs]

end MultiplicativeIdealWeight

end TauCeti
