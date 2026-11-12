/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.NumberField.DirichletDensity

import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import TauCeti.Analysis.SpecialFunctions.Log.NegLogOneSub
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Convergence
import TauCeti.NumberTheory.ArithmeticDirichletSeries.ResidueDegree
import TauCeti.RingTheory.DedekindDomain.PrimesAbove

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
  yields a nonnegative `tsum` (and for `s ≤ 0` the `tsum` is `0`); convergence is supplied
  separately for `s > 1 / 2`.
* `TauCeti.tsum_neg_log_one_sub_sub_absNorm_rpow_le`: it is at most `2 [K : ℚ]` for every
  `s ≥ 1`; together the two bound the sum in `[0, 2 [K : ℚ]]` on `s ≥ 1`.
* `TauCeti.tendsto_tsum_neg_log_one_sub_sub_absNorm_rpow`: as `s → 1⁺` the sum tends to its
  value at `s = 1`, by dominated convergence against `∑_𝔭 N(𝔭) ^ (-2)`.
* `TauCeti.abs_tsum_neg_log_one_sub_sub_primeIdealZetaSum_le`: for `s > 1`, where the
  two sums converge separately, the sum of the Euler-factor logarithms differs from
  `NumberField.Set.primeIdealZetaSum Set.univ s` by at most `2 [K : ℚ]`.

## Implementation notes

The constant is explicit rather than existentially quantified, and the upper bound's hypothesis
is the closed condition `1 ≤ s` rather than a neighbourhood of `1`: both are free here, and a
consumer that wants an eventual statement near `s = 1` gets it by weakening, whereas the
converse costs work.

The two halves carry different hypotheses on purpose. The `tsum` is nonnegative for every real
`s`, with no hypothesis: for `0 < s` the terms are termwise nonnegative, since
`N(𝔭) ^ (-s) < 1`, and for `s ≤ 0` the family is not summable, so the `tsum` is `0` by convention.
The uniform upper bound uses `N(𝔭) ^ (-s) ≤ 1 / 2`. No uniform bound can persist as
`s ↓ 1 / 2`, where the dominating prime series approaches its convergence endpoint.

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

open Filter IsDedekindDomain NumberField
open scoped NumberField Topology

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

/-- **The prime-power tail has nonnegative sum.** For `s > 0` the terms are nonnegative, so the
`tsum` is nonnegative. This statement does not assert summability, which is supplied by
`TauCeti.summable_neg_log_one_sub_sub_absNorm_rpow` for `s > 1 / 2`. For `s ≤ 0` the terms are
bounded above by `-1` off a finite set of primes, so the family is not summable and the `tsum` is
`0`. -/
theorem tsum_neg_log_one_sub_sub_absNorm_rpow_nonneg {s : ℝ} :
    0 ≤ ∑' 𝔭 : HeightOneSpectrum (𝓞 K), (-Real.log (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) -
      (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) := by
  rcases lt_or_ge 0 s with hs | hs
  · exact tsum_nonneg fun 𝔭 ↦ Real.neg_log_one_sub_rpow_sub_nonneg
      (one_lt_two.trans_le (two_le_absNorm_asIdeal_real 𝔭)) hs
  rw [tsum_eq_zero_of_not_summable]
  intro hsum
  -- Off the primes of norm at most `B`, every term is at most `-1`.
  obtain ⟨B, hB⟩ : ∃ B : ℕ, ∀ 𝔭 : HeightOneSpectrum (𝓞 K), B < Ideal.absNorm 𝔭.asIdeal →
      -Real.log (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) -
        (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) ≤ -1 := by
    rcases hs.eq_or_lt with rfl | hlt
    · exact ⟨0, fun 𝔭 _ ↦ by simp⟩
    · refine ⟨⌈(2 : ℝ) ^ (-s)⁻¹⌉₊, fun 𝔭 hlt' ↦ ?_⟩
      have hN : (2 : ℝ) ^ (-s)⁻¹ ≤ Ideal.absNorm 𝔭.asIdeal :=
        (Nat.le_ceil _).trans (by exact_mod_cast hlt'.le)
      have hy : 2 ≤ (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) :=
        (Real.rpow_inv_le_iff_of_pos (by positivity) (by positivity) (neg_pos.mpr hlt)).mp hN
      have hlog : 0 ≤ Real.log (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) := by
        rw [← neg_sub, Real.log_neg_eq_log]
        exact Real.log_nonneg (by linarith)
      linarith
  have hfin := (Ring.HasFiniteQuotients.finite_absNorm_heightOneSpectrum_le (S := 𝓞 K) B)
  have hinf : Infinite (HeightOneSpectrum (𝓞 K)) :=
    haveI : Infinite (HeightOneSpectrum ℤ) :=
      Infinite.of_surjective Rat.HeightOneSpectrum.primesEquiv
        Rat.HeightOneSpectrum.primesEquiv.surjective
    Infinite.of_surjective (HeightOneSpectrum.under ℤ) (HeightOneSpectrum.under_surjective ℤ (𝓞 K))
  have hlim := hsum.tendsto_cofinite_zero
  obtain ⟨𝔭, h1, h2⟩ := ((hlim.eventually (Metric.ball_mem_nhds 0 one_pos)).and
    (hfin.eventually_cofinite_notMem)).exists
  have := hB 𝔭 (by simpa using h2)
  rw [Real.dist_eq, sub_zero, abs_lt] at h1
  linarith [h1.1]

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

/-- **The prime-power tail is continuous at `s = 1` from the right.** As `s → 1⁺`, the sum
`∑_𝔭 (-log (1 - N(𝔭) ^ (-s)) - N(𝔭) ^ (-s))` tends to its value at `s = 1`, by dominated
convergence against `∑_𝔭 N(𝔭) ^ (-2)`. -/
theorem tendsto_tsum_neg_log_one_sub_sub_absNorm_rpow :
    Tendsto (fun s : ℝ ↦ ∑' 𝔭 : HeightOneSpectrum (𝓞 K),
        (-Real.log (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) -
          (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s))) (𝓝[>] 1)
      (𝓝 (∑' 𝔭 : HeightOneSpectrum (𝓞 K),
        (-Real.log (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ)⁻¹) - (Ideal.absNorm 𝔭.asIdeal : ℝ)⁻¹))) := by
  refine tendsto_tsum_of_dominated_convergence
    (bound := fun 𝔭 ↦ (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-(2 : ℝ)))
    (summable_absNorm_rpow_primes_of_one_lt one_lt_two) (fun 𝔭 ↦ ?_) ?_
  · have h2 := two_le_absNorm_asIdeal_real 𝔭
    have hN : (Ideal.absNorm 𝔭.asIdeal : ℝ) ≠ 0 := (zero_lt_two.trans_le h2).ne'
    have hpos : 1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-(1 : ℝ)) ≠ 0 := by
      rw [Real.rpow_neg_one]
      exact (sub_pos.mpr (inv_lt_one_of_one_lt₀ (one_lt_two.trans_le h2))).ne'
    have hr : ContinuousAt (fun s : ℝ ↦ (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) 1 :=
      (Real.continuousAt_const_rpow hN).comp continuousAt_neg
    have hc : ContinuousAt (fun s : ℝ ↦ -Real.log (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) -
        (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) 1 :=
      ((continuousAt_const.sub hr).log hpos).neg.sub hr
    simpa only [Real.rpow_neg_one] using hc.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s) 𝔭
    rw [Real.norm_of_nonneg (Real.neg_log_one_sub_rpow_sub_nonneg
      (one_lt_two.trans_le (two_le_absNorm_asIdeal_real 𝔭)) (zero_lt_one.trans hs))]
    exact Real.neg_log_one_sub_rpow_sub_le (two_le_absNorm_asIdeal_real 𝔭) hs.le

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
    abs_of_nonneg TauCeti.tsum_neg_log_one_sub_sub_absNorm_rpow_nonneg]
  exact TauCeti.tsum_neg_log_one_sub_sub_absNorm_rpow_le hs.le

end TauCeti
