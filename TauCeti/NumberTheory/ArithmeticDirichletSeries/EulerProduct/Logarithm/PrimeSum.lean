/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.Deriv

import Mathlib.NumberTheory.EulerProduct.ExpLog
import TauCeti.Analysis.Calculus.BoundedOfDerivContinuousAt
import TauCeti.Analysis.SpecialFunctions.Log.NegLogOneSub
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Convergence
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Estimates
import TauCeti.NumberTheory.ArithmeticDirichletSeries.ResidueDegree

/-!
# Prime sums of a bounded multiplicative weight

For a completely multiplicative ideal weight `w` of a number field `K`, this file names two
Dirichlet series over the height-one primes `𝔭` of `𝓞 K`:

* the prime sum `∑_𝔭 w(𝔭) N(𝔭)⁻ˢ`, `TauCeti.MultiplicativeIdealWeight.primeSum`;
* the prime-power sum `∑_{𝔭, e} (w(𝔭) N(𝔭)⁻ˢ) ^ (e + 1) / (e + 1)`,
  `TauCeti.MultiplicativeIdealWeight.primePowSum`, which on `Re s > 1` is a logarithm of the
  `L`-series of `w`.

For a weight bounded by `1`, the two differ by at most `2 [K : ℚ]` on real `s > 1`. If moreover
the `L`-series agrees on `Re s > 1` with a function analytic and nonzero at `s = 1`, the
prime-power sum is a primitive of its logarithmic derivative, which is continuous at `1`; so both
sums stay bounded as `s → 1⁺`.

## Main results

* `TauCeti.MultiplicativeIdealWeight.norm_primePowSum_sub_primeSum_le`: for real `t > 1`, the
  prime-power sum differs from the prime sum by at most `2 [K : ℚ]`.
* `TauCeti.MultiplicativeIdealWeight.hasDerivAt_primePowSum`: on `Re z > 1` the prime-power sum
  differentiates to the logarithmic derivative of any function agreeing there with the `L`-series.
* `TauCeti.MultiplicativeIdealWeight.exists_norm_primePowSum_le` and
  `TauCeti.MultiplicativeIdealWeight.exists_norm_primeSum_le`: if the `L`-series continues to a
  function analytic and nonzero at `1`, both sums are bounded as `t → 1⁺`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
-/

public section

open Filter IsDedekindDomain
open scoped NumberField nonZeroDivisors Topology

namespace TauCeti.MultiplicativeIdealWeight

open IdealArithmeticFunction

variable {K : Type*} [Field K] [NumberField K]

/-- The prime sum `∑_𝔭 w(𝔭) N(𝔭)⁻ˢ` of a multiplicative ideal weight, over the height-one primes
of `𝓞 K`. -/
noncomputable def primeSum (w : MultiplicativeIdealWeight K) (s : ℂ) : ℂ :=
  ∑' P : HeightOneSpectrum (𝓞 K), w P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s

/-- The prime-power sum `∑_{𝔭, e} (w(𝔭) N(𝔭)⁻ˢ) ^ (e + 1) / (e + 1)` of a multiplicative ideal
weight: the expansion of `∑_𝔭 -log (1 - w(𝔭) N(𝔭)⁻ˢ)` over the height-one primes of `𝓞 K`
and the exponents. -/
noncomputable def primePowSum (w : MultiplicativeIdealWeight K) (s : ℂ) : ℂ :=
  ∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
    (w pe.1.asIdeal / (Ideal.absNorm pe.1.asIdeal : ℂ) ^ s) ^ (pe.2 + 1) / ((pe.2 : ℂ) + 1)

/-- The defining sum of `TauCeti.MultiplicativeIdealWeight.primeSum`. -/
theorem primeSum_def (w : MultiplicativeIdealWeight K) (s : ℂ) :
    w.primeSum s =
      ∑' P : HeightOneSpectrum (𝓞 K), w P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s :=
  (rfl)

/-- The defining sum of `TauCeti.MultiplicativeIdealWeight.primePowSum`. -/
theorem primePowSum_def (w : MultiplicativeIdealWeight K) (s : ℂ) :
    w.primePowSum s = ∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
      (w pe.1.asIdeal / (Ideal.absNorm pe.1.asIdeal : ℂ) ^ s) ^ (pe.2 + 1) / ((pe.2 : ℂ) + 1) :=
  (rfl)

variable {w : MultiplicativeIdealWeight K}

/-- A weight bounded by `1` gives an ideal arithmetic function bounded by `1`. -/
theorem norm_toIdealArithmeticFunction_le_one (hw : ∀ I : Ideal (𝓞 K), ‖w I‖ ≤ 1)
    (I : (Ideal (𝓞 K))⁰) : ‖w.toIdealArithmeticFunction I‖ ≤ 1 := by
  simpa using hw I

/-- For a weight bounded by `1` and real `t ≥ 1`, the local ratio `w(𝔭) N(𝔭)⁻ᵗ` has norm at most
`N(𝔭)⁻¹`. -/
theorem norm_div_absNorm_cpow_le (hw : ∀ I : Ideal (𝓞 K), ‖w I‖ ≤ 1)
    (P : HeightOneSpectrum (𝓞 K)) {t : ℝ} (ht : 1 ≤ t) :
    ‖w P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ (t : ℂ)‖ ≤ (Ideal.absNorm P.asIdeal : ℝ)⁻¹ := by
  have hN : (1 : ℝ) ≤ Ideal.absNorm P.asIdeal := one_le_two.trans (two_le_absNorm_asIdeal_real P)
  rw [norm_div, Complex.norm_natCast_cpow_of_pos (by exact_mod_cast zero_lt_one.trans_le hN),
    Complex.ofReal_re]
  calc ‖w P.asIdeal‖ / (Ideal.absNorm P.asIdeal : ℝ) ^ t
      ≤ 1 / (Ideal.absNorm P.asIdeal : ℝ) ^ (1 : ℝ) := by
        gcongr
        exact hw _
    _ = (Ideal.absNorm P.asIdeal : ℝ)⁻¹ := by rw [Real.rpow_one, one_div]

/-- **The prime-power tail is bounded.** For a weight bounded by `1` and real `t > 1`, the
prime-power sum differs from the prime sum by at most `2 [K : ℚ]`. -/
theorem norm_primePowSum_sub_primeSum_le (hw : ∀ I : Ideal (𝓞 K), ‖w I‖ ≤ 1) {t : ℝ}
    (ht : 1 < t) : ‖w.primePowSum t - w.primeSum t‖ ≤ 2 * Module.finrank ℚ K := by
  have hs := summable_idealTerm_of_bounded_of_one_lt_re (norm_toIdealArithmeticFunction_le_one hw)
    (s := t) (by simpa using ht)
  have hr := w.summable_div_of_summable_idealTerm hs
  -- Regroup the prime-power expansion prime by prime into Euler-factor logarithms.
  rw [primePowSum, w.tsum_prime_pow_eq_tsum_neg_log_one_sub hs, primeSum,
    ← hr.clog_one_sub.neg.tsum_sub hr]
  refine (tsum_of_norm_bounded (summable_absNorm_rpow_primes_of_one_lt one_lt_two).hasSum
    fun P ↦ ?_).trans tsum_absNorm_rpow_neg_two_le
  have hx := norm_div_absNorm_cpow_le hw P ht.le
  refine (Complex.norm_neg_log_one_sub_sub_le (hx.trans ?_)).trans ?_
  · rw [one_div]
    exact inv_anti₀ two_pos (two_le_absNorm_asIdeal_real P)
  · rw [Real.rpow_neg (by positivity), Real.rpow_two, ← inv_pow]
    gcongr

/-- **The prime-power sum is a logarithm of the `L`-series.** For a weight bounded by `1`, on
`Re z > 1` the prime-power sum differentiates to the logarithmic derivative of any function `C`
agreeing there with the `L`-series of `w`. -/
theorem hasDerivAt_primePowSum (hw : ∀ I : Ideal (𝓞 K), ‖w I‖ ≤ 1) {C : ℂ → ℂ}
    (hCL : ∀ z : ℂ, 1 < z.re → C z = LSeries (normCoeff K w.toIdealArithmeticFunction) z) {z : ℂ}
    (hz : 1 < z.re) : HasDerivAt w.primePowSum (logDeriv C z) z := by
  have habs :=
    idealAbscissaOfAbsConv_lt_re_of_bounded (norm_toIdealArithmeticFunction_le_one hw) hz
  have heq : C =ᶠ[𝓝 z] LSeries (normCoeff K w.toIdealArithmeticFunction) :=
    eventually_of_mem ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz) hCL
  rw [logDeriv_apply, heq.deriv_eq, heq.eq_of_nhds, ← logDeriv_apply,
    w.logDeriv_LSeries_eq_tsum_prime_pow habs]
  exact w.hasDerivAt_tsum_prime_pow habs

/-- **A logarithm of a continued `L`-series stays bounded.** If the `L`-series of a weight bounded
by `1` agrees on `Re s > 1` with a function analytic and nonzero at `s = 1`, then its prime-power
sum is bounded as `t → 1⁺`. -/
theorem exists_norm_primePowSum_le (hw : ∀ I : Ideal (𝓞 K), ‖w I‖ ≤ 1) {C : ℂ → ℂ}
    (hC : AnalyticAt ℂ C 1) (hC1 : C 1 ≠ 0)
    (hCL : ∀ z : ℂ, 1 < z.re → C z = LSeries (normCoeff K w.toIdealArithmeticFunction) z) :
    ∃ B, ∀ᶠ t : ℝ in 𝓝[>] 1, ‖w.primePowSum t‖ ≤ B := by
  refine exists_norm_le_of_hasDerivWithinAt_of_continuousWithinAt
    (f := fun t : ℝ ↦ w.primePowSum t) (g := fun u : ℝ ↦ logDeriv C u) ?_
    (eventually_nhdsWithin_of_forall fun u hu ↦
      (hasDerivAt_primePowSum hw hCL (by simpa using hu)).comp_ofReal.hasDerivWithinAt)
  have hlog : ContinuousAt (logDeriv C) ((1 : ℝ) : ℂ) := by
    simpa [logDeriv] using hC.deriv.continuousAt.div hC.continuousAt hC1
  exact (hlog.comp Complex.continuous_ofReal.continuousAt).continuousWithinAt

/-- **The prime sum of a continued `L`-series stays bounded.** If the `L`-series of a weight
bounded by `1` agrees on `Re s > 1` with a function analytic and nonzero at `s = 1`, then its prime
sum is bounded as `t → 1⁺`. -/
theorem exists_norm_primeSum_le (hw : ∀ I : Ideal (𝓞 K), ‖w I‖ ≤ 1) {C : ℂ → ℂ}
    (hC : AnalyticAt ℂ C 1) (hC1 : C 1 ≠ 0)
    (hCL : ∀ z : ℂ, 1 < z.re → C z = LSeries (normCoeff K w.toIdealArithmeticFunction) z) :
    ∃ B, ∀ᶠ t : ℝ in 𝓝[>] 1, ‖w.primeSum t‖ ≤ B := by
  obtain ⟨B, hB⟩ := exists_norm_primePowSum_le hw hC hC1 hCL
  refine ⟨B + 2 * Module.finrank ℚ K, ?_⟩
  filter_upwards [hB, self_mem_nhdsWithin] with t hBt (ht : 1 < t)
  calc ‖w.primeSum t‖ ≤ ‖w.primePowSum t‖ + ‖w.primePowSum t - w.primeSum t‖ :=
        norm_le_insert _ _
    _ ≤ _ := add_le_add hBt (norm_primePowSum_sub_primeSum_le hw ht)

end TauCeti.MultiplicativeIdealWeight
