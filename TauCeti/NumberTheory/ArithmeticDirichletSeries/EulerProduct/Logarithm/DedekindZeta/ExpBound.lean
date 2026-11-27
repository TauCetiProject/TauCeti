/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import TauCeti.NumberTheory.NumberField.ResidueDegree
import TauCeti.Analysis.SpecialFunctions.Log.NegLogOneSub
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Convergence
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Estimates
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.DedekindZeta.Basic
import TauCeti.NumberTheory.ArithmeticDirichletSeries.ResidueDegree

/-!
# An exponential bound for the Dedekind zeta function at `s ≥ 2`

For a number field `K` of degree `d = [K : ℚ]` and real `s ≥ 2`, the Dedekind zeta function
satisfies `log ζ_K(s) ≤ 2 ^ (3 - s) d`, so `ζ_K(s) ≤ exp (2 ^ (3 - s) d)`, and in particular
`ζ_K(s) ≤ exp (2 d)`. Consequently, for every finite set `S` of integral ideals,
`∑_{𝔟 ∈ S} N(𝔟) ^ (-s) ≤ exp (2 d)`. The bounds depend on `K` only through its degree.

The proof takes logarithms in the Euler product,
`log ζ_K(s) = ∑_𝔭 -log (1 - N(𝔭) ^ (-s))`
(`TauCeti.log_dedekindZeta_re_eq_tsum_neg_log_one_sub`). Each local ratio `x = N(𝔭) ^ (-s)` is
at most `1 / 2`, where `-log (1 - x) ≤ 2 x` (`Real.neg_log_one_sub_le_two_mul`), and
`x ≤ 2 ^ (2 - s) N(𝔭) ^ (-2)` because `N(𝔭) ≥ 2`, so
`log ζ_K(s) ≤ 2 ^ (3 - s) ∑_𝔭 N(𝔭) ^ (-2)`. At most `d` primes lie over each rational prime `p`,
each of norm at least `p`, so `∑_𝔭 N(𝔭) ^ (-2) ≤ d ∑_{m ≥ 2} m ^ (-2) ≤ d`
(`TauCeti.tsum_absNorm_rpow_neg_two_le`). The finite sums over integral ideals are then bounded
through `TauCeti.sum_absNorm_rpow_neg_le_dedekindZeta_re`.

## Main results

* `TauCeti.log_dedekindZeta_re_le_two_rpow_mul_finrank`: `log ζ_K(s) ≤ 2 ^ (3 - s) [K : ℚ]` for
  real `s ≥ 2`.
* `TauCeti.log_dedekindZeta_re_le_two_mul_finrank`: `log ζ_K(s) ≤ 2 [K : ℚ]` for real `s ≥ 2`.
* `TauCeti.dedekindZeta_re_le_exp_two_mul_finrank`: `ζ_K(s) ≤ exp (2 [K : ℚ])` for real `s ≥ 2`.
* `TauCeti.sum_absNorm_rpow_neg_le_exp_two_mul_finrank`: a finite sum of `N(𝔟) ^ (-s)` over
  integral ideals is at most `exp (2 [K : ℚ])`, for real `s ≥ 2`.

## References

* The bound `ζ_E(2) ≤ exp (2 [E : ℚ])` is used, in this form, for the sum over frequencies in the
  shorter formal proof of the Riemann hypothesis for Dirichlet `L`-functions
  (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC; file
  `src/New/Spanning/MainTerm/Frequencies.lean`, declaration `New.sum_absNorm_inv_sq_le`), where it
  is derived from a general bound on the logarithm of Euler products. The proof here is a direct
  one from the Euler product of `ζ_K`.
* J. Neukirch, *Algebraic Number Theory*, Chapter I, Proposition 8.2, and Chapter VII, §5.
-/

public section

open IsDedekindDomain NumberField
open scoped NumberField

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K]

/-- **The logarithm of the Dedekind zeta function at `s ≥ 2` is at most `2 ^ (3 - s)` times the
degree.** For real `s ≥ 2`, `log ζ_K(s) ≤ 2 ^ (3 - s) [K : ℚ]`. -/
theorem log_dedekindZeta_re_le_two_rpow_mul_finrank {s : ℝ} (hs : 2 ≤ s) :
    Real.log (dedekindZeta K s).re ≤ 2 ^ (3 - s) * Module.finrank ℚ K := by
  -- Splitting the exponent `-s` as `(2 - s) + (-2)` leaves the exponent `-2`, summed by
  -- `TauCeti.tsum_absNorm_rpow_neg_two_le`, and the nonpositive exponent `2 - s`, where
  -- `N(𝔭) ≥ 2` gives `N(𝔭) ^ (2 - s) ≤ 2 ^ (2 - s)`.
  have h_split : -s = (2 - s) + -2 := by ring
  -- Splitting `3 - s` as `1 + (2 - s)` absorbs the factor `2` of `-log (1 - x) ≤ 2 x`.
  have h_succ : 3 - s = 1 + (2 - s) := by ring
  have h_local (𝔭 : HeightOneSpectrum (𝓞 K)) :
      -Real.log (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) ≤
        2 ^ (3 - s) * (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-(2 : ℝ)) := by
    have h2 : (2 : ℝ) ≤ Ideal.absNorm 𝔭.asIdeal := two_le_absNorm_asIdeal_real 𝔭
    refine (Real.neg_log_one_sub_le_two_mul (by positivity)
      (𝔭.absNorm_rpow_neg_le_half (by linarith))).trans ?_
    rw [h_split, Real.rpow_add (by positivity), h_succ, Real.rpow_add two_pos, Real.rpow_one,
      mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos two_pos h2 (by linarith)) (by positivity)) zero_le_two
  rw [log_dedekindZeta_re_eq_tsum_neg_log_one_sub (by linarith)]
  calc ∑' 𝔭 : HeightOneSpectrum (𝓞 K), -Real.log (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s))
    _ ≤ ∑' 𝔭 : HeightOneSpectrum (𝓞 K),
        2 ^ (3 - s) * (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-(2 : ℝ)) :=
      (summable_neg_log_one_sub_absNorm_rpow (by linarith)).tsum_le_tsum h_local
        ((summable_absNorm_rpow_primes_of_one_lt one_lt_two).mul_left _)
    _ = 2 ^ (3 - s) * ∑' 𝔭 : HeightOneSpectrum (𝓞 K),
        (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-(2 : ℝ)) := tsum_mul_left
    _ ≤ 2 ^ (3 - s) * Module.finrank ℚ K := by
      gcongr
      exact tsum_absNorm_rpow_neg_two_le

/-- **The logarithm of the Dedekind zeta function at `s ≥ 2` is at most twice the degree.** -/
theorem log_dedekindZeta_re_le_two_mul_finrank {s : ℝ} (hs : 2 ≤ s) :
    Real.log (dedekindZeta K s).re ≤ 2 * Module.finrank ℚ K := by
  refine (log_dedekindZeta_re_le_two_rpow_mul_finrank hs).trans ?_
  gcongr
  calc (2 : ℝ) ^ (3 - s) ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
    _ = 2 := Real.rpow_one 2

/-- **The Dedekind zeta function at `s ≥ 2` is at most `exp (2 [K : ℚ])`.** -/
theorem dedekindZeta_re_le_exp_two_mul_finrank {s : ℝ} (hs : 2 ≤ s) :
    (dedekindZeta K s).re ≤ Real.exp (2 * Module.finrank ℚ K) :=
  (Real.log_le_iff_le_exp (dedekindZeta_re_pos (by linarith))).1
    (log_dedekindZeta_re_le_two_mul_finrank hs)

/-- **Finite sums of `N(𝔟) ^ (-s)` are at most `exp (2 [K : ℚ])`.** For real `s ≥ 2` and every
finite set `S` of integral ideals of `𝓞 K`, `∑_{𝔟 ∈ S} N(𝔟) ^ (-s) ≤ exp (2 [K : ℚ])`. -/
theorem sum_absNorm_rpow_neg_le_exp_two_mul_finrank {s : ℝ} (hs : 2 ≤ s)
    (S : Finset (Ideal (𝓞 K))) :
    ∑ 𝔟 ∈ S, (Ideal.absNorm 𝔟 : ℝ) ^ (-s) ≤ Real.exp (2 * Module.finrank ℚ K) :=
  (sum_absNorm_rpow_neg_le_dedekindZeta_re (by linarith) S).trans
    (dedekindZeta_re_le_exp_two_mul_finrank hs)

end TauCeti
