/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Stieltjes
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.AbelSummation
import Mathlib.Topology.Algebra.Order.Floor

/-!
# Summatory functions as Stieltjes functions

A partial sum `A(x) = ∑_{N i ≤ x} w i` of a nonnegative real weight over a Northcott carrier is a
monotone step function, and with the inclusive cutoff it is continuous from the right: it jumps
by `∑_{N i = n} w i` exactly at each natural number `n`, and the value at `n` already includes
the jump. It is therefore a Stieltjes function, and the associated measure `dA` is the weighted
sum of point masses `∑ i, w i δ_{N i}`.

This is the language in which analytic number theory usually writes sums over integers, ideals
or primes: `∑_{a < N i ≤ b} w i g (N i) = ∫_{(a, b]} g dA`. Here that identity is a theorem about
Mathlib's `StieltjesFunction.measure`, for an arbitrary function `g` with values in a real Banach
space. Combined with Abel summation it gives the Stieltjes integration-by-parts formula
`∫_{(a, b]} g dA = g(b) A(b) - g(a) A(a) - ∫_a^b g'(t) A(t) dt`.

For the prime counts of a number field this recovers the classical pair
`π_S(x) = ∫_{(1, x]} dϑ_S(t) / log t` and `ϑ_S(x) = ∫_{(1, x]} log t dπ_S(t)`, valid for every
real cutoff `x`.

## Main definitions

* `TauCeti.summatoryStieltjes`: the summatory function of a nonnegative real weight, as a
  `StieltjesFunction ℝ`.
* `TauCeti.primeThetaStieltjes` and `TauCeti.primeCountStieltjes`: the weighted and unweighted
  prime counts of a set of primes, as Stieltjes functions.

## Main results

* `TauCeti.continuousWithinAt_summatory_Ici`: a summatory function is continuous from the right.
* `TauCeti.measure_summatoryStieltjes`: the Stieltjes measure is `∑ i, w i • δ_{N i}`.
* `TauCeti.restrict_Ioc_measure_summatoryStieltjes`: on `(a, b]` it is the finite sum of the point
  masses of the indices of `N`-value in `(a, b]`.
* `TauCeti.setIntegral_Ioc_summatoryStieltjes`: `∫_{(a, b]} g dA` is the increment between `a` and
  `b` of the summatory function of `i ↦ w i • g (N i)`.
* `TauCeti.setIntegral_Ioc_summatoryStieltjes_eq_sub_sub_integral`: Abel summation as Stieltjes
  integration by parts.
* `TauCeti.primeCount_eq_integral_primeThetaStieltjes` and
  `TauCeti.primeTheta_eq_integral_primeCountStieltjes`: `dπ_S = dϑ_S / log t` and
  `dϑ_S = log t dπ_S` in integrated form.

## References

* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter I.0.
-/

public section

namespace TauCeti

open MeasureTheory Set Filter
open scoped Topology NumberField
open IsDedekindDomain

variable {ι : Type*} (N : ι → ℕ) [Northcott N]

/-! ### Right continuity -/

/-- A summatory function is continuous from the right: it is constant on each interval
`[n, n + 1)` with `n` an integer, because the cutoff is inclusive. -/
theorem continuousWithinAt_summatory_Ici {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
    (w : ι → M) (x : ℝ) : ContinuousWithinAt (summatory N w) (Ici x) x := by
  refine continuousWithinAt_const.congr_of_eventuallyEq ?_ rfl
  filter_upwards [tendsto_pure.mp (tendsto_floor_right_pure_floor x)] with y hy
  rw [summatory_apply, summatory_apply, normLE_eq_normLE_of_floor_eq N hy]

/-! ### The Stieltjes function and its measure -/

/-- The summatory function `x ↦ ∑_{N i ≤ x} w i` of a nonnegative real weight, as a Stieltjes
function. -/
noncomputable def summatoryStieltjes {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) : StieltjesFunction ℝ where
  toFun := summatory N w
  mono' := summatory_mono N hw
  right_continuous' := continuousWithinAt_summatory_Ici N w

/-- The Stieltjes function `summatoryStieltjes N hw` evaluates to the summatory function. -/
@[simp]
theorem summatoryStieltjes_apply {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (x : ℝ) :
    summatoryStieltjes N hw x = summatory N w x := (rfl)

/-- **The Stieltjes measure of a summatory function** is the sum over the carrier of the point
masses at the `N`-values, weighted by `w`. -/
theorem measure_summatoryStieltjes {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) :
    (summatoryStieltjes N hw).measure =
      Measure.sum fun i ↦ ENNReal.ofReal (w i) • Measure.dirac (N i : ℝ) := by
  refine Measure.ext_of_Ioc _ _ fun a b hab ↦ ?_
  rw [StieltjesFunction.measure_Ioc, summatoryStieltjes_apply, summatoryStieltjes_apply,
    summatory_sub_summatory_eq_sum_filter N w hab.le,
    ENNReal.ofReal_sum_of_nonneg fun i _ ↦ hw i, Measure.sum_apply _ measurableSet_Ioc]
  simp only [Measure.smul_apply, Measure.dirac_apply' _ measurableSet_Ioc, smul_eq_mul]
  rw [tsum_eq_sum (s := {j ∈ normLE N b | a < N j}) fun i hi ↦ ?_]
  · refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [indicator_of_mem ((mem_normLE_filter_lt N).mp hi), Pi.one_apply, mul_one]
  · rw [indicator_of_notMem (fun h ↦ hi ((mem_normLE_filter_lt N).mpr h)), mul_zero]

/-- On the interval `(a, b]` the Stieltjes measure of a summatory function is the finite sum of
the weighted point masses of the indices whose `N`-value lies in `(a, b]`. -/
theorem restrict_Ioc_measure_summatoryStieltjes {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (a b : ℝ) :
    (summatoryStieltjes N hw).measure.restrict (Ioc a b) =
      ∑ i ∈ {j ∈ normLE N b | a < N j}, ENNReal.ofReal (w i) • Measure.dirac (N i : ℝ) := by
  ext s hs
  rw [Measure.restrict_apply hs, measure_summatoryStieltjes,
    Measure.sum_apply _ (hs.inter measurableSet_Ioc), Measure.finsetSum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply' _ (hs.inter measurableSet_Ioc),
    Measure.dirac_apply' _ hs, smul_eq_mul]
  rw [tsum_eq_sum (s := {j ∈ normLE N b | a < N j}) fun i hi ↦ ?_]
  · refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hmem := (mem_normLE_filter_lt N).mp hi
    by_cases his : (N i : ℝ) ∈ s
    · rw [indicator_of_mem (mem_inter his hmem), indicator_of_mem his]
    · rw [indicator_of_notMem (fun h ↦ his h.1), indicator_of_notMem his]
  · rw [indicator_of_notMem (fun h ↦ hi ((mem_normLE_filter_lt N).mpr h.2)), mul_zero]

/-! ### Integrals against the Stieltjes measure -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Sums as Stieltjes integrals.** For `a ≤ b`, integrating `g` over `(a, b]` against the
Stieltjes measure `dA` of `A = summatory N w` gives `∑_{a < N i ≤ b} w i • g (N i)`, written as
the increment between `a` and `b` of the summatory function of `i ↦ w i • g (N i)`. -/
theorem setIntegral_Ioc_summatoryStieltjes {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (g : ℝ → E)
    {a b : ℝ} (hab : a ≤ b) :
    ∫ t in Ioc a b, g t ∂(summatoryStieltjes N hw).measure =
      summatory N (fun i ↦ w i • g (N i)) b - summatory N (fun i ↦ w i • g (N i)) a := by
  rw [restrict_Ioc_measure_summatoryStieltjes, summatory_sub_summatory_eq_sum_filter N _ hab,
    integral_finsetSum_measure fun i _ ↦
      (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hw i)]

/-- Sums as Stieltjes integrals from a cutoff `a` below every `N`-value: then
`∫_{(a, x]} g dA = ∑_{N i ≤ x} w i • g (N i)` for every real `x`. -/
theorem setIntegral_Ioc_summatoryStieltjes_of_lt {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (g : ℝ → E)
    {a : ℝ} (hN : ∀ i, a < N i) (x : ℝ) :
    ∫ t in Ioc a x, g t ∂(summatoryStieltjes N hw).measure =
      summatory N (fun i ↦ w i • g (N i)) x := by
  have hzero {y : ℝ} (hy : y ≤ a) : normLE N y = ∅ :=
    Finset.eq_empty_of_forall_notMem fun i hi ↦
      (hy.trans_lt (hN i)).not_ge ((mem_normLE N).mp hi)
  rcases le_or_gt a x with hax | hxa
  · rw [setIntegral_Ioc_summatoryStieltjes N hw g hax, summatory_apply N _ a, hzero le_rfl,
      Finset.sum_empty, sub_zero]
  · rw [Ioc_eq_empty_of_le hxa.le, Measure.restrict_empty, integral_zero_measure,
      summatory_apply, hzero hxa.le, Finset.sum_empty]

/-- **Abel summation as Stieltjes integration by parts.** For nonnegative cutoffs `a ≤ b` and a
function `g` differentiable on `[a, b]` with integrable derivative,
`∫_{(a, b]} g dA = g(b) A(b) - g(a) A(a) - ∫_a^b g'(t) A(t) dt`, where `A = summatory N w`. -/
theorem setIntegral_Ioc_summatoryStieltjes_eq_sub_sub_integral {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    {g : ℝ → ℝ} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hg_diff : ∀ t ∈ Icc a b, DifferentiableAt ℝ g t) (hg_int : IntegrableOn (deriv g) (Icc a b)) :
    ∫ t in Ioc a b, g t ∂(summatoryStieltjes N hw).measure =
      g b * summatory N w b - g a * summatory N w a -
        ∫ t in Ioc a b, deriv g t * summatory N w t := by
  simpa only [setIntegral_Ioc_summatoryStieltjes N hw g hab, smul_eq_mul] using
    summatory_mul_eq_sub_sub_integral_mul N w ha hab hg_diff hg_int

/-! ### The prime counts of a number field -/

variable {K : Type*} [Field K] [NumberField K]

variable (K) in
/-- The logarithmically weighted prime count `ϑ_S` of a set `S` of primes, as a Stieltjes
function. -/
noncomputable def primeThetaStieltjes (S : Set (HeightOneSpectrum (𝓞 K))) :
    StieltjesFunction ℝ :=
  summatoryStieltjes (fun v : HeightOneSpectrum (𝓞 K) ↦ Ideal.absNorm v.asIdeal)
    (w := S.indicator fun v ↦ Real.log (Ideal.absNorm v.asIdeal : ℝ))
    (indicator_nonneg fun v _ ↦ log_absNorm_asIdeal_nonneg v)

variable (K) in
/-- The prime count `π_S` of a set `S` of primes, as a Stieltjes function. -/
noncomputable def primeCountStieltjes (S : Set (HeightOneSpectrum (𝓞 K))) :
    StieltjesFunction ℝ :=
  summatoryStieltjes (fun v : HeightOneSpectrum (𝓞 K) ↦ Ideal.absNorm v.asIdeal)
    (w := S.indicator 1) (indicator_nonneg fun _ _ ↦ zero_le_one)

/-- The Stieltjes function `primeThetaStieltjes K S` evaluates to `ϑ_S`. -/
@[simp]
theorem primeThetaStieltjes_apply (S : Set (HeightOneSpectrum (𝓞 K))) (x : ℝ) :
    primeThetaStieltjes K S x = primeTheta K S x := by
  rw [primeThetaStieltjes, summatoryStieltjes_apply, primeTheta_apply, summatory_apply]

/-- The Stieltjes function `primeCountStieltjes K S` evaluates to `π_S`. -/
@[simp]
theorem primeCountStieltjes_apply (S : Set (HeightOneSpectrum (𝓞 K))) (x : ℝ) :
    primeCountStieltjes K S x = primeCount K S x := by
  rw [primeCountStieltjes, summatoryStieltjes_apply, primeCount_apply, summatory_apply]

/-- Every prime has absolute norm greater than `1`, so integrals from `1` see every prime. -/
private theorem one_lt_absNorm_asIdeal (v : HeightOneSpectrum (𝓞 K)) :
    (1 : ℝ) < Ideal.absNorm v.asIdeal :=
  one_lt_two.trans_le (two_le_absNorm_asIdeal_real v)

/-- **`π_S` from `ϑ_S` as a Stieltjes integral:** `π_S(x) = ∫_{(1, x]} dϑ_S(t) / log t` for every
real cutoff `x`. -/
theorem primeCount_eq_integral_primeThetaStieltjes (S : Set (HeightOneSpectrum (𝓞 K))) (x : ℝ) :
    primeCount K S x = ∫ t in Ioc 1 x, (Real.log t)⁻¹ ∂(primeThetaStieltjes K S).measure := by
  rw [← primeCountStieltjes_apply, primeCountStieltjes, summatoryStieltjes_apply,
    primeThetaStieltjes, setIntegral_Ioc_summatoryStieltjes_of_lt _ _ _ one_lt_absNorm_asIdeal]
  refine congrArg (summatory _ · x) (funext fun v ↦ ?_)
  by_cases hv : v ∈ S
  · rw [indicator_of_mem hv, indicator_of_mem hv, Pi.one_apply, smul_eq_mul,
      mul_inv_cancel₀ (log_absNorm_asIdeal_pos v).ne']
  · rw [indicator_of_notMem hv, indicator_of_notMem hv, zero_smul]

/-- **`ϑ_S` from `π_S` as a Stieltjes integral:** `ϑ_S(x) = ∫_{(1, x]} log t dπ_S(t)` for every
real cutoff `x`. -/
theorem primeTheta_eq_integral_primeCountStieltjes (S : Set (HeightOneSpectrum (𝓞 K))) (x : ℝ) :
    primeTheta K S x = ∫ t in Ioc 1 x, Real.log t ∂(primeCountStieltjes K S).measure := by
  rw [← primeThetaStieltjes_apply, primeThetaStieltjes, summatoryStieltjes_apply,
    primeCountStieltjes, setIntegral_Ioc_summatoryStieltjes_of_lt _ _ _ one_lt_absNorm_asIdeal]
  refine congrArg (summatory _ · x) (funext fun v ↦ ?_)
  by_cases hv : v ∈ S
  · rw [indicator_of_mem hv, indicator_of_mem hv, Pi.one_apply, one_smul]
  · rw [indicator_of_notMem hv, indicator_of_notMem hv, zero_smul]

end TauCeti
