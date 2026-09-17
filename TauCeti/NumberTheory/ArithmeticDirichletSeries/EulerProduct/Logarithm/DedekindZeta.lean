/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.DedekindZeta
import TauCeti.Analysis.SpecialFunctions.Log.NegLogOneSub
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.Basic
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Convergence
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Counting

/-!
# The real Euler product of the Dedekind zeta function in exponential form

For real `s > 1`, every local ratio `x = N(𝔭) ^ (-s)` of a height-one prime lies in `(0, 1/2]`,
because `N(𝔭) ≥ 2`. The principal logarithm of each Euler factor is then the real number
`-log (1 - x)`, and the exponential form
`TauCeti.MultiplicativeIdealWeight.exp_tsum_neg_log_one_sub_eq_LSeries` of the Euler product,
specialized to the trivial weight, becomes a statement about real numbers: `ζ_K(s)` is the
exponential of the convergent real sum `∑_𝔭 -log (1 - N(𝔭) ^ (-s))`. In particular `ζ_K(s)` is a
positive real number, and that sum is its real logarithm.

## Main results

* `TauCeti.absNorm_rpow_neg_le_half`: `N(𝔭) ^ (-s) ≤ 1/2` for `1 ≤ s`.
* `TauCeti.summable_neg_log_one_sub_absNorm_rpow`: `∑_𝔭 -log (1 - N(𝔭) ^ (-s))` converges for
  `1 < s`.
* `TauCeti.dedekindZeta_ofReal_eq_exp_tsum_neg_log_one_sub`: for real `s > 1`, `ζ_K(s)` is the
  exponential of that real sum.
* `TauCeti.dedekindZeta_re_eq_exp` and `TauCeti.dedekindZeta_re_pos`: the same for the real part,
  which is therefore positive.
* `TauCeti.log_dedekindZeta_re_eq_tsum_neg_log_one_sub`: that real sum is the real logarithm of
  `ζ_K(s)`.

## References

* The real logarithmic identity also appears, under the same name, in the
  Birkbeck–Brasca Chebotarev density project, <https://github.com/CBirkbeck/chebotarev-density>
  (Apache-2.0), commit `8575c9df1ae0a61120ab5c964c7911414254bec7`, file
  `CebotarevDensity/Density.lean`, where it is proved from `Real.hasProd_of_hasSum_log` and the
  product formula. It is derived here instead from TauCeti's exponential Euler product
  `TauCeti.MultiplicativeIdealWeight.exp_tsum_neg_log_one_sub_eq_LSeries`.
-/

public section

open IsDedekindDomain NumberField

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K]

/-- For `1 ≤ s`, the local ratio `N(𝔭) ^ (-s)` of a height-one prime is at most `1/2`, because
`N(𝔭) ≥ 2`. -/
theorem absNorm_rpow_neg_le_half (P : HeightOneSpectrum (𝓞 K)) {s : ℝ} (hs : 1 ≤ s) :
    (Ideal.absNorm P.asIdeal : ℝ) ^ (-s) ≤ 1 / 2 := by
  have h2 := two_le_absNorm_asIdeal_real P
  calc (Ideal.absNorm P.asIdeal : ℝ) ^ (-s) ≤ (Ideal.absNorm P.asIdeal : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ ≤ 1 / 2 := by
        rw [Real.rpow_neg_one, one_div]
        exact inv_anti₀ (by norm_num) h2

/-- For `1 < s`, the real logarithms `-log (1 - N(𝔭) ^ (-s))` of the Euler factors of the Dedekind
zeta function are summable over the height-one primes. -/
theorem summable_neg_log_one_sub_absNorm_rpow {s : ℝ} (hs : 1 < s) :
    Summable fun P : HeightOneSpectrum (𝓞 K) ↦
      -Real.log (1 - (Ideal.absNorm P.asIdeal : ℝ) ^ (-s)) := by
  refine ((summable_absNorm_rpow_primes_of_one_lt hs).mul_left 2).of_nonneg_of_le
    (fun P ↦ (Real.rpow_nonneg (Nat.cast_nonneg _) _).trans
      (Real.le_neg_log_one_sub (by linarith [absNorm_rpow_neg_le_half P hs.le]))) (fun P ↦ ?_)
  -- On `[0, 1/2]`, `x + 2 x ^ 2 ≤ 2 x`.
  have hx0 : 0 ≤ (Ideal.absNorm P.asIdeal : ℝ) ^ (-s) := by positivity
  have hx := absNorm_rpow_neg_le_half P hs.le
  nlinarith [Real.neg_log_one_sub_le_add_two_mul_sq hx0 hx]

/-- **The real Euler product of the Dedekind zeta function in exponential form.** For real
`s > 1`, `ζ_K(s)` is the exponential of the convergent real sum
`∑_𝔭 -log (1 - N(𝔭) ^ (-s))` over the height-one primes of `𝓞 K`. In particular `ζ_K(s)` is a
positive real number, and that sum is its real logarithm.

This is `TauCeti.MultiplicativeIdealWeight.exp_tsum_neg_log_one_sub_eq_LSeries` for the trivial
weight, with each principal logarithm identified with a real one. -/
theorem dedekindZeta_ofReal_eq_exp_tsum_neg_log_one_sub {s : ℝ} (hs : 1 < s) :
    dedekindZeta K s = (Real.exp (∑' P : HeightOneSpectrum (𝓞 K),
      -Real.log (1 - (Ideal.absNorm P.asIdeal : ℝ) ^ (-s))) : ℂ) := by
  have hsum : Summable
      (idealTerm K (1 : MultiplicativeIdealWeight K).toIdealArithmeticFunction (s : ℂ)) := by
    rw [MultiplicativeIdealWeight.toIdealArithmeticFunction_one]
    exact summable_idealTerm_one_iff.mpr (by simpa using hs)
  rw [dedekindZeta_eq_LSeries_normCoeff_one,
    ← MultiplicativeIdealWeight.toIdealArithmeticFunction_one,
    ← MultiplicativeIdealWeight.exp_tsum_neg_log_one_sub_eq_LSeries _ hsum, Complex.ofReal_exp,
    Complex.ofReal_tsum]
  congr 1
  refine tsum_congr fun P ↦ ?_
  have hpos : 0 ≤ 1 - (Ideal.absNorm P.asIdeal : ℝ) ^ (-s) := by
    linarith [absNorm_rpow_neg_le_half P hs.le]
  rw [Complex.ofReal_neg, Complex.ofReal_log hpos, MultiplicativeIdealWeight.one_apply,
    ite_eq_right P.ne_bot]
  push_cast [Complex.ofReal_cpow (Nat.cast_nonneg _)]
  rw [Complex.cpow_neg, one_div]

/-- For real `s > 1`, the real part of `ζ_K(s)` is the exponential of `∑_𝔭 -log (1 - N(𝔭) ^ (-s))`.
-/
theorem dedekindZeta_re_eq_exp {s : ℝ} (hs : 1 < s) :
    (dedekindZeta K s).re = Real.exp (∑' P : HeightOneSpectrum (𝓞 K),
      -Real.log (1 - (Ideal.absNorm P.asIdeal : ℝ) ^ (-s))) := by
  rw [dedekindZeta_ofReal_eq_exp_tsum_neg_log_one_sub hs, Complex.ofReal_re]

/-- **The real logarithm of the Dedekind zeta function.** For real `s > 1`, the real logarithm of
`ζ_K(s)` is the convergent sum `∑_𝔭 -log (1 - N(𝔭) ^ (-s))` over the height-one primes of `𝓞 K`.
-/
theorem log_dedekindZeta_re_eq_tsum_neg_log_one_sub {s : ℝ} (hs : 1 < s) :
    Real.log (dedekindZeta K s).re = ∑' P : HeightOneSpectrum (𝓞 K),
      -Real.log (1 - (Ideal.absNorm P.asIdeal : ℝ) ^ (-s)) := by
  rw [dedekindZeta_re_eq_exp hs, Real.log_exp]

/-- For real `s > 1`, the real part of `ζ_K(s)` is positive. -/
theorem dedekindZeta_re_pos {s : ℝ} (hs : 1 < s) : 0 < (dedekindZeta K s).re := by
  rw [dedekindZeta_re_eq_exp hs]
  exact Real.exp_pos _

end TauCeti
