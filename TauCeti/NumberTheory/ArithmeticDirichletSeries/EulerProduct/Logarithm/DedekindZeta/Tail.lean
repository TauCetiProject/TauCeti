/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.NumberField.DirichletDensity

import TauCeti.Analysis.SpecialFunctions.Log.NegLogOneSub
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Convergence
import TauCeti.NumberTheory.ArithmeticDirichletSeries.ResidueDegree

/-!
# The higher prime powers in the logarithm of the Dedekind Euler product

Taking logarithms in the Euler product `ζ_K(s) = ∏_𝔭 (1 - N(𝔭) ^ (-s))⁻¹` turns it into the
double sum `∑_𝔭 ∑_{m ≥ 1} N(𝔭) ^ (-m s) / m`, whose `m = 1` part is the prime Dirichlet series
`NumberField.Set.primeIdealZetaSum Set.univ s`.  This file bounds everything else: the `m ≥ 2`
part, equivalently the difference `∑_𝔭 (-log (1 - N(𝔭) ^ (-s)) - N(𝔭) ^ (-s))`, is nonnegative
and at most `2 [K : ℚ]`.

The bound is uniform on all of `s ≥ 1`, endpoint included, and that endpoint is the whole point:
at `s = 1` the Euler-factor logarithm sum and the prime Dirichlet series each diverge, while
their termwise difference still converges, because discarding the linear term of
`-log (1 - x)` replaces the exponent `-s` by the exponent `-2 s`, and `2 s ≥ 2` already
converges.

Two elementary inputs carry the argument.

* A height-one prime `𝔭` has `N(𝔭) ≥ 2`, so `N(𝔭) ^ (-s) ≤ 1 / 2` for `s ≥ 1` and the
  denominator `1 - N(𝔭) ^ (-s)` is bounded below by `1 / 2`; the termwise difference is
  therefore at most `N(𝔭) ^ (-2)`.
* `N(𝔭)` is at least the rational prime below `𝔭` and at most `[K : ℚ]` primes lie over one
  rational prime, so `∑_𝔭 N(𝔭) ^ (-2) ≤ 2 [K : ℚ]`.  That bound is not proved again here: it is
  the imported `TauCeti.tsum_absNorm_rpow_neg_two_le`.

## Main results

* `TauCeti.summable_neg_log_one_sub_sub_absNorm_rpow`: the termwise difference between the
  Euler-factor logarithm and the prime Dirichlet term is summable for every `s > 1 / 2`.
* `TauCeti.tsum_neg_log_one_sub_sub_absNorm_rpow_nonneg`: termwise nonnegativity for `s > 0`
  yields a nonnegative `tsum`; convergence is supplied separately for `s > 1 / 2`.
* `TauCeti.tsum_neg_log_one_sub_sub_absNorm_rpow_le`: it is at most `2 [K : ℚ]` for every
  `s ≥ 1`; together the two bound the sum in `[0, 2 [K : ℚ]]` on `s ≥ 1`.
* `TauCeti.abs_tsum_neg_log_one_sub_sub_primeIdealZetaSum_le`: for `s > 1`, where the
  two sums converge separately, the sum of the Euler-factor logarithms differs from
  `NumberField.Set.primeIdealZetaSum Set.univ s` by at most `2 [K : ℚ]`.

## Implementation notes

The constant is explicit rather than existentially quantified, and the upper bound's hypothesis
is the closed condition `1 ≤ s` rather than a neighbourhood of `1`: both are free here, and a
consumer that wants an eventual statement near `s = 1` gets it by weakening, whereas the
converse costs work.

The two halves carry different hypotheses on purpose. Nonnegativity holds as soon as
`N(𝔭) ^ (-s) < 1`, so it is stated on `0 < s`; the uniform upper bound uses
`N(𝔭) ^ (-s) ≤ 1 / 2`. No uniform bound can persist as `s ↓ 1 / 2`, where the dominating
prime series approaches its convergence endpoint.

The one-variable estimate behind the termwise bound is not proved again: it is Mathlib's
`Complex.norm_log_one_sub_inv_sub_self_le` read along the reals, which is where the factor `2`
in the denominator below comes from.

Convergence of `∑_𝔭 N(𝔭) ^ (-s)` over all height-one primes for `1 < s` is not proved again
either: it is `TauCeti.summable_absNorm_rpow_primes_of_one_lt`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
* J.-P. Serre, *A Course in Arithmetic*, Chapter VI, §3.
* C. Birkbeck and R. Brasca, `CebotarevDensity/Density.lean` in
  [CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density), Apache-2.0,
  commit `8575c9df1ae0a61120ab5c964c7911414254bec7`, declarations
  `primeIdealZetaHigherTail_bounded` and `neg_log_one_sub_sub_le`.
-/

public section

open IsDedekindDomain NumberField
open scoped NumberField

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K]

/-! ### The prime-power tail -/

/-- **The prime-power tail is summable.** The termwise difference between the Euler-factor
logarithm `-log (1 - N(𝔭) ^ (-s))` and the prime Dirichlet term `N(𝔭) ^ (-s)` is summable for
every `s > 1 / 2`; at `s = 1` this remains summable although either of the two families from which
it is built is not. -/
theorem summable_neg_log_one_sub_sub_absNorm_rpow {s : ℝ} (hs : 1 / 2 < s) :
    Summable fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦
      -Real.log (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) -
        (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) := by
  have hs0 : 0 < s := by linarith
  have hs2 : 1 < 2 * s := by linarith
  have hsum := (summable_absNorm_rpow_primes_of_one_lt (K := K) hs2).mul_left
    ((2 * (1 - (2 : ℝ) ^ (-s)))⁻¹)
  refine hsum.of_nonneg_of_le
    (fun 𝔭 ↦ Real.neg_log_one_sub_rpow_sub_nonneg
      (one_lt_two.trans_le (two_le_absNorm_asIdeal_real 𝔭)) hs0) ?_
  intro 𝔭
  simpa only [div_eq_mul_inv, mul_comm] using
    Real.neg_log_one_sub_rpow_sub_le_div (two_le_absNorm_asIdeal_real 𝔭) hs0

/-- **The prime-power tail is termwise nonnegative.** For every `s > 0`, termwise nonnegativity
yields a nonnegative `tsum`. This statement does not assert summability; that is supplied by
`TauCeti.summable_neg_log_one_sub_sub_absNorm_rpow` for `s > 1 / 2`. -/
theorem tsum_neg_log_one_sub_sub_absNorm_rpow_nonneg {s : ℝ} (hs : 0 < s) :
    0 ≤ ∑' 𝔭 : HeightOneSpectrum (𝓞 K), (-Real.log (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) -
      (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) :=
  tsum_nonneg fun 𝔭 ↦ Real.neg_log_one_sub_rpow_sub_nonneg
    (one_lt_two.trans_le (two_le_absNorm_asIdeal_real 𝔭)) hs

/-- **The prime-power tail is bounded uniformly on `s ≥ 1`.** The constant `2 [K : ℚ]` does not
depend on `s`, so this survives the passage to the limit `s → 1⁺` that the Dirichlet-density
normalization needs. -/
theorem tsum_neg_log_one_sub_sub_absNorm_rpow_le {s : ℝ} (hs : 1 ≤ s) :
    ∑' 𝔭 : HeightOneSpectrum (𝓞 K), (-Real.log (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) -
      (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) ≤ 2 * Module.finrank ℚ K :=
  ((summable_neg_log_one_sub_sub_absNorm_rpow (K := K)
      ((by norm_num : (1 / 2 : ℝ) < 1).trans_le hs)).tsum_le_tsum
    (fun 𝔭 ↦ Real.neg_log_one_sub_rpow_sub_le (two_le_absNorm_asIdeal_real 𝔭) hs)
    (summable_absNorm_rpow_primes_of_one_lt one_lt_two)).trans tsum_absNorm_rpow_neg_two_le

/-- **The Euler-factor logarithms sum to the prime Dirichlet series up to `O(1)`.** For `s > 1`,
where both series converge, `∑_𝔭 -log (1 - N(𝔭) ^ (-s))` differs from
`NumberField.Set.primeIdealZetaSum Set.univ s` by at most the constant `2 [K : ℚ]`.

The absolute value is here so that the statement can be used directly as an `O(1)` estimate; the
difference is in fact nonnegative — see `TauCeti.tsum_neg_log_one_sub_sub_absNorm_rpow_nonneg`. -/
theorem abs_tsum_neg_log_one_sub_sub_primeIdealZetaSum_le {s : ℝ} (hs : 1 < s) :
    |(∑' 𝔭 : HeightOneSpectrum (𝓞 K), -Real.log (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s))) -
      NumberField.Set.primeIdealZetaSum
        (Set.univ : Set (HeightOneSpectrum (𝓞 K))) s| ≤ 2 * Module.finrank ℚ K := by
  have hsumP := TauCeti.summable_absNorm_rpow_primes_of_one_lt (K := K) hs
  have hsumL : Summable fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦
      -Real.log (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) := by
    simpa using (TauCeti.summable_neg_log_one_sub_sub_absNorm_rpow (K := K)
      ((by norm_num : (1 / 2 : ℝ) < 1).trans hs)).add hsumP
  -- Both series converge separately, so their difference is the sum of the prime-power tail.
  rw [NumberField.Set.primeIdealZetaSum_def, tsum_univ fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦
      (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s), ← hsumL.tsum_sub hsumP,
    abs_of_nonneg (TauCeti.tsum_neg_log_one_sub_sub_absNorm_rpow_nonneg (zero_lt_one.trans hs))]
  exact TauCeti.tsum_neg_log_one_sub_sub_absNorm_rpow_le hs.le

end TauCeti
