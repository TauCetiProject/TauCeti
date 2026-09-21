/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.SpecialFunctions.Log.InvLog
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.AbelSummation
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Counting

/-!
# Abel summation for norm-indexed summatory functions

Mathlib's `sum_mul_eq_sub_sub_integral_mul` is Abel summation for a sequence indexed by the natural
numbers.  Every counting argument of the arithmetic-Dirichlet-series roadmap instead sums a weight
over a carrier indexed by ideals or by height-one primes, cut off inclusively by the absolute norm.
This file supplies the bridge: the weight is regrouped into its norm fibres, Mathlib's identity is
applied to the resulting sequence, and the answer is read back as an equation between
`TauCeti.summatory` functions.

The bridge is stated for a general Northcott index `N : ι → ℕ`, because Layer 6 uses it for both
the ideal carrier and the prime carrier.  The integral runs over the half-open interval `Set.Ioc`,
so each boundary term is counted exactly once, as the roadmap's conventions table demands.

## Main results

* `TauCeti.summatory_mul_eq_sub_sub_integral_mul`: Abel summation between two nonnegative real
  cutoffs for a weight of the form `i ↦ w i * g (N i)`.
* `TauCeti.summatory_mul_eq_sub_integral_mul_of_le`: Abel summation from a real lower bound,
  with `TauCeti.summatory_mul_eq_sub_integral_mul_of_one_le` and
  `TauCeti.summatory_mul_eq_sub_integral_mul_of_two_le` naming the cutoffs `1` and `2`.
* `TauCeti.idealSummatory_mul_eq_sub_integral_mul`: the cutoff-`1` form for nonzero ideals.
* `TauCeti.primeSummatory_mul_eq_sub_integral_mul`: the cutoff-`2` form for the height-one primes
  of a number field.
* `TauCeti.norm_summatory_mul_cpow_le_of_summatory_le`: an imaginary-power twist preserves a
  positive power bound for partial sums, with an explicit constant.
* `TauCeti.integrableOn_mul_summatory`: a summatory function times an integrable factor is
  integrable on a compact interval, so the integrals above are genuine.
* `TauCeti.summatory_mul_le_of_summatory_le` and `TauCeti.tsum_mul_le_of_summatory_le`: for a
  nonnegative nonincreasing `g` and a carrier whose indices all have `N`-value at least `a ≥ 0`,
  an upper bound `C` on the partial sums of `w` gives the upper bound `C * g a` for the twisted
  partial sums and series.  This is how an eventual comparison of
  counting functions becomes a comparison of Dirichlet series uniform in `s`.
* `TauCeti.primeTheta_eq_log_mul_primeCount_sub_integral` and
  `TauCeti.primeCount_eq_primeTheta_div_log_add_integral`: the two exact Abel identities relating
  the roadmap's weighted prime counts,
  `ϑ(x) = π(x) log x - ∫_2^x π(t)/t dt` and `π(x) = ϑ(x)/log x + ∫_2^x ϑ(t)/(t log²t) dt`.
  Both hold for every real cutoff; below `2` all three terms vanish.

## Roadmap role

This is Layer **6.1** of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`: Mathlib's exact
finite identity is consumed, not restated, and only the norm-indexed bridges are added.  The two
prime identities are the finite input to Layer 6.2, which turns `ϑ(x) ∼ δx` into `π(x) ∼ δ Li(x)`
by estimating the integrals appearing here.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 1.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter I.2.
-/

public section

namespace TauCeti

open MeasureTheory
open scoped nonZeroDivisors NumberField
open IsDedekindDomain

variable {ι : Type*} (N : ι → ℕ) [Northcott N] {𝕜 : Type*} [RCLike 𝕜]

/-! ### Regrouping a weight into its norm fibres -/

/-- The sequence of fibre sums attached to a weight: the total weight of the indices of
`N`-value exactly `n`.  This is the sequence handed to Mathlib's Abel summation. -/
private noncomputable def normFiberSum (w : ι → 𝕜) (n : ℕ) : 𝕜 :=
  ∑ i ∈ normLE N (n : ℝ) with N i = n, w i

private theorem normFiberSum_eq_sum_filter (w : ι → 𝕜) (n : ℕ) {x : ℝ} (hx : (n : ℝ) ≤ x) :
    normFiberSum N w n = ∑ i ∈ normLE N x with N i = n, w i := by
  refine Finset.sum_congr ?_ fun _ _ ↦ rfl
  ext i
  simp only [Finset.mem_filter, mem_normLE, and_congr_left_iff]
  rintro rfl
  simp [hx]

private theorem normFiberSum_mul (w : ι → 𝕜) (g : ℝ → 𝕜) (n : ℕ) :
    normFiberSum N (fun i ↦ w i * g (N i)) n = g n * normFiberSum N w n := by
  simp only [normFiberSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [(Finset.mem_filter.mp hi).2, mul_comm]

/-- A summatory function is the partial sum of the sequence of fibre sums. -/
private theorem summatory_eq_sum_Icc_normFiberSum (w : ι → 𝕜) {x : ℝ} (hx : 0 ≤ x) :
    summatory N w x = ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, normFiberSum N w n := by
  have hmaps : ∀ i ∈ normLE N x, N i ∈ Finset.Icc 0 ⌊x⌋₊ := fun i hi ↦
    Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.le_floor ((mem_normLE N).mp hi)⟩
  rw [summatory_apply, ← Finset.sum_fiberwise_of_maps_to hmaps w]
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  exact (normFiberSum_eq_sum_filter N w n
    (le_trans (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).2) (Nat.floor_le hx))).symm

private theorem sum_Ioc_normFiberSum (w : ι → 𝕜) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, normFiberSum N w n = summatory N w b - summatory N w a := by
  have hfloor : ⌊a⌋₊ ≤ ⌊b⌋₊ := Nat.floor_le_floor hab
  have hdisj : Disjoint (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊) (Finset.Icc 0 ⌊a⌋₊) := by
    refine Finset.disjoint_left.mpr fun n hn hn' ↦ ?_
    simp only [Finset.mem_Ioc] at hn
    simp only [Finset.mem_Icc] at hn'
    omega
  have hunion : Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ ∪ Finset.Icc 0 ⌊a⌋₊ = Finset.Icc 0 ⌊b⌋₊ := by
    ext n
    simp only [Finset.mem_union, Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [summatory_eq_sum_Icc_normFiberSum N w (ha.trans hab),
    summatory_eq_sum_Icc_normFiberSum N w ha, eq_sub_iff_add_eq, ← Finset.sum_union hdisj, hunion]

/-! ### Abel summation over a Northcott carrier -/

/-- **Abel summation for a norm-indexed summatory function.**  For a weight `w` on the index type
and a function `g` differentiable on `[a, b]`, the summatory function of the twisted weight
`i ↦ w i * g (N i)` between the inclusive cutoffs `a` and `b` is the boundary term
`g b · A(b) - g a · A(a)` minus the integral of `g' · A`, where `A = summatory N w`.

This is Mathlib's `sum_mul_eq_sub_sub_integral_mul` read through the norm fibres of `N`. -/
theorem summatory_mul_eq_sub_sub_integral_mul (w : ι → 𝕜) {g : ℝ → 𝕜} {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hg_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ g t)
    (hg_int : IntegrableOn (deriv g) (Set.Icc a b)) :
    summatory N (fun i ↦ w i * g (N i)) b - summatory N (fun i ↦ w i * g (N i)) a =
      g b * summatory N w b - g a * summatory N w a -
        ∫ t in Set.Ioc a b, deriv g t * summatory N w t := by
  have key := sum_mul_eq_sub_sub_integral_mul (normFiberSum N w) ha hab hg_diff hg_int
  have hL : ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, g (n : ℝ) * normFiberSum N w n =
      summatory N (fun i ↦ w i * g (N i)) b - summatory N (fun i ↦ w i * g (N i)) a := by
    simp_rw [← normFiberSum_mul N w g]
    exact sum_Ioc_normFiberSum N _ ha hab
  have hI : ∫ t in Set.Ioc a b, deriv g t * ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, normFiberSum N w n =
      ∫ t in Set.Ioc a b, deriv g t * summatory N w t :=
    setIntegral_congr_fun measurableSet_Ioc fun t ht ↦ by
      rw [summatory_eq_sum_Icc_normFiberSum N w (ha.trans ht.1.le)]
  rw [hL, ← summatory_eq_sum_Icc_normFiberSum N w (ha.trans hab),
    ← summatory_eq_sum_Icc_normFiberSum N w ha, hI] at key
  exact key

private theorem summatory_mul_eq_mul_summatory_of_le {a : ℝ} (ha : ∀ i, a ≤ N i) (w : ι → 𝕜)
    (g : ℝ → 𝕜) :
    summatory N (fun i ↦ w i * g (N i)) a = g a * summatory N w a := by
  rw [summatory_apply, summatory_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [le_antisymm ((mem_normLE N).mp hi) (ha i), mul_comm]

/-- Abel summation from a real cutoff `a` for a carrier all of whose indices have `N`-value at
least `a`. The boundary term at `a` cancels, because there the twisted weight is `g a` times the
untwisted one.

The identity holds for every cutoff `b`: below `a` all three terms vanish. -/
theorem summatory_mul_eq_sub_integral_mul_of_le {a : ℝ} (ha : 0 ≤ a)
    (hN : ∀ i, a ≤ (N i : ℝ)) (w : ι → 𝕜) {g : ℝ → 𝕜} (b : ℝ)
    (hg_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ g t)
    (hg_int : IntegrableOn (deriv g) (Set.Icc a b)) :
    summatory N (fun i ↦ w i * g (N i)) b =
      g b * summatory N w b - ∫ t in Set.Ioc a b, deriv g t * summatory N w t := by
  rcases lt_or_ge b a with hb | hb
  · rw [summatory_eq_zero_of_lt N hN hb, summatory_eq_zero_of_lt N hN hb,
      Set.Ioc_eq_empty_of_le hb.le]
    simp
  · have key := summatory_mul_eq_sub_sub_integral_mul N w ha hb hg_diff hg_int
    rw [summatory_mul_eq_mul_summatory_of_le N hN w g] at key
    linear_combination key

/-- Abel summation from the cutoff `1` for a carrier all of whose indices have `N`-value at least
`1`, such as the nonzero ideals of a number field. -/
theorem summatory_mul_eq_sub_integral_mul_of_one_le (h1 : ∀ i, 1 ≤ (N i : ℝ)) (w : ι → 𝕜)
    {g : ℝ → 𝕜} (b : ℝ) (hg_diff : ∀ t ∈ Set.Icc 1 b, DifferentiableAt ℝ g t)
    (hg_int : IntegrableOn (deriv g) (Set.Icc 1 b)) :
    summatory N (fun i ↦ w i * g (N i)) b =
      g b * summatory N w b - ∫ t in Set.Ioc 1 b, deriv g t * summatory N w t :=
  summatory_mul_eq_sub_integral_mul_of_le N zero_le_one h1 w b hg_diff hg_int

/-- Abel summation from the cutoff `2` for a carrier all of whose indices have `N`-value at least
`2`, such as the height-one primes of a number field.  The boundary term at `2` cancels, because
there the twisted weight is `g 2` times the untwisted one.

The identity holds for every cutoff `b`: below `2` all three terms vanish. -/
theorem summatory_mul_eq_sub_integral_mul_of_two_le (h2 : ∀ i, 2 ≤ (N i : ℝ)) (w : ι → 𝕜)
    {g : ℝ → 𝕜}
    (b : ℝ) (hg_diff : ∀ t ∈ Set.Icc 2 b, DifferentiableAt ℝ g t)
    (hg_int : IntegrableOn (deriv g) (Set.Icc 2 b)) :
    summatory N (fun i ↦ w i * g (N i)) b =
      g b * summatory N w b - ∫ t in Set.Ioc 2 b, deriv g t * summatory N w t :=
  summatory_mul_eq_sub_integral_mul_of_le N (by norm_num) h2 w b hg_diff hg_int

/-- A summatory function, multiplied by a factor integrable on a compact interval of nonnegative
cutoffs, is integrable there. -/
theorem integrableOn_mul_summatory (w : ι → 𝕜) {f : ℝ → 𝕜} {a b : ℝ} (ha : 0 ≤ a)
    (hf : IntegrableOn f (Set.Icc a b)) :
    IntegrableOn (fun t ↦ f t * summatory N w t) (Set.Icc a b) :=
  (integrableOn_mul_sum_Icc (normFiberSum N w) ha hf).congr_fun
    (fun t ht ↦ by rw [summatory_eq_sum_Icc_normFiberSum N w (ha.trans ht.1)]) measurableSet_Icc

/-! ### Imaginary-power twists -/

private theorem differentiableAt_ofReal_cpow_neg (z : ℂ) (hz : z ≠ 0) {t : ℝ} (ht : 0 < t) :
    DifferentiableAt ℝ (fun u : ℝ ↦ (u : ℂ) ^ (-z)) t :=
  differentiableAt_id.ofReal_cpow_const (by simpa only [id_eq] using ht.ne')
    (neg_ne_zero.mpr hz)

private theorem deriv_ofReal_cpow_neg (z : ℂ) (hz : z ≠ 0) {t : ℝ} (ht : 0 < t) :
    deriv (fun u : ℝ ↦ (u : ℂ) ^ (-z)) t = -z * (t : ℂ) ^ (-z - 1) :=
  Complex.deriv_ofReal_cpow_const ht.ne' (neg_ne_zero.mpr hz)

private theorem integrableOn_deriv_ofReal_cpow_neg (z : ℂ) (hz : z ≠ 0) (x : ℝ) :
    IntegrableOn (deriv fun t : ℝ ↦ (t : ℂ) ^ (-z)) (Set.Icc 1 x) := by
  refine (ContinuousOn.integrableOn_Icc fun t ht ↦ ?_).congr_fun
    (fun t ht ↦ (deriv_ofReal_cpow_neg z hz (by linarith [ht.1])).symm) measurableSet_Icc
  exact continuousWithinAt_const.mul
    (Complex.continuousAt_ofReal_cpow_const t (-z - 1)
      (Or.inr (by linarith [ht.1]))).continuousWithinAt

private theorem norm_ofReal_cpow_neg (z : ℂ) (hz : z.re = 0) {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ (-z)‖ = 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.neg_re, hz, neg_zero, Real.rpow_zero]

private theorem norm_deriv_ofReal_cpow_neg (z : ℂ) (hz : z.re = 0) (hz0 : z ≠ 0)
    {t : ℝ} (ht : 0 < t) :
    ‖deriv (fun u : ℝ ↦ (u : ℂ) ^ (-z)) t‖ = ‖z‖ * t⁻¹ := by
  rw [deriv_ofReal_cpow_neg z hz0 ht, norm_mul, norm_neg,
    Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.sub_re, Complex.neg_re, Complex.one_re, hz,
    show -0 - 1 = (-1 : ℝ) by ring, Real.rpow_neg_one]

/-- **An imaginary-power Abel bound.** Suppose every index has `N`-value at least `1`, and the
partial sums of `w` are bounded by `C * t ^ θ` for a positive exponent `θ`. Twisting the weight
by `(N i) ^ (-z)` with `Re z = 0` preserves that exponent, at the cost of the explicit factor
`1 + ‖z‖ / θ`. -/
theorem norm_summatory_mul_cpow_le_of_summatory_le (hN : ∀ i, 1 ≤ (N i : ℝ)) (w : ι → ℂ)
    {C θ x : ℝ} (hx : 1 ≤ x) (hθ : 0 < θ) (z : ℂ) (hz : z.re = 0)
    (hC : ∀ t, 1 ≤ t → ‖summatory N w t‖ ≤ C * t ^ θ) :
    ‖summatory N (fun i ↦ w i * (N i : ℂ) ^ (-z)) x‖ ≤
      C * (1 + ‖z‖ / θ) * x ^ θ := by
  rcases eq_or_ne z 0 with rfl | hz0
  · simpa using hC x hx
  let g : ℝ → ℂ := fun t ↦ (t : ℂ) ^ (-z)
  have hg_diff : ∀ t ∈ Set.Icc (1 : ℝ) x, DifferentiableAt ℝ g t :=
    fun t ht ↦ differentiableAt_ofReal_cpow_neg z hz0 (by linarith [ht.1])
  have hg_int : IntegrableOn (deriv g) (Set.Icc (1 : ℝ) x) :=
    integrableOn_deriv_ofReal_cpow_neg z hz0 x
  have hformula : summatory N (fun i ↦ w i * (N i : ℂ) ^ (-z)) x =
      g x * summatory N w x - ∫ t in Set.Ioc 1 x, deriv g t * summatory N w t := by
    have hcast : ∀ i, ((N i : ℝ) : ℂ) = (N i : ℂ) := fun _ ↦ by norm_num
    simpa only [g, hcast] using
      summatory_mul_eq_sub_integral_mul_of_one_le N hN w x hg_diff hg_int
  have hC0 : 0 ≤ C :=
    (norm_nonneg (summatory N w 1)).trans (by simpa using hC 1 le_rfl)
  have hbound_int :
      ‖∫ t in Set.Ioc 1 x, deriv g t * summatory N w t‖ ≤
        (‖z‖ * C / θ) * x ^ θ := by
    rw [← intervalIntegral.integral_of_le hx]
    calc
      ‖∫ t in (1 : ℝ)..x, deriv g t * summatory N w t‖
          ≤ ∫ t in (1 : ℝ)..x, (‖z‖ * C) * t ^ (θ - 1) := by
            refine intervalIntegral.norm_integral_le_of_norm_le hx ?_
              ((intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul _)
            filter_upwards with t
            intro ht
            have ht0 : 0 < t := by linarith [ht.1]
            have hinv : 0 ≤ t⁻¹ := inv_nonneg.mpr ht0.le
            calc
              ‖deriv g t * summatory N w t‖ =
                  ‖z‖ * t⁻¹ * ‖summatory N w t‖ := by
                    rw [norm_mul, norm_deriv_ofReal_cpow_neg z hz hz0 ht0]
              _ ≤ ‖z‖ * t⁻¹ * (C * t ^ θ) :=
                    mul_le_mul_of_nonneg_left (hC t ht.1.le)
                      (mul_nonneg (norm_nonneg _) hinv)
              _ = ‖z‖ * C * t ^ (θ - 1) := by
                rw [show θ - 1 = θ + (-1 : ℝ) by ring, Real.rpow_add ht0,
                  Real.rpow_neg_one]
                ring
      _ = (‖z‖ * C) * ((x ^ θ - 1) / θ) := by
        rw [intervalIntegral.integral_const_mul,
          integral_rpow (Or.inl (by linarith)), sub_add_cancel, Real.one_rpow]
      _ ≤ (‖z‖ * C / θ) * x ^ θ := by
        have hzC : 0 ≤ ‖z‖ * C := mul_nonneg (norm_nonneg _) hC0
        calc
          (‖z‖ * C) * ((x ^ θ - 1) / θ) ≤ (‖z‖ * C) * (x ^ θ / θ) :=
            mul_le_mul_of_nonneg_left
              (div_le_div_of_nonneg_right (sub_le_self _ zero_le_one) hθ.le) hzC
          _ = (‖z‖ * C / θ) * x ^ θ := by ring
  rw [hformula]
  calc
    ‖g x * summatory N w x - ∫ t in Set.Ioc 1 x, deriv g t * summatory N w t‖
        ≤ ‖g x‖ * ‖summatory N w x‖ +
          ‖∫ t in Set.Ioc 1 x, deriv g t * summatory N w t‖ := by
            simpa only [norm_mul] using
              (norm_sub_le (g x * summatory N w x)
                (∫ t in Set.Ioc 1 x, deriv g t * summatory N w t))
    _ ≤ C * x ^ θ + (‖z‖ * C / θ) * x ^ θ := by
      rw [show ‖g x‖ = 1 from norm_ofReal_cpow_neg z hz (zero_lt_one.trans_le hx), one_mul]
      exact add_le_add (hC x hx) hbound_int
    _ = C * (1 + ‖z‖ / θ) * x ^ θ := by ring

/-! ### One-sided bounds for twisted sums -/

/-- **A one-sided Abel bound.**  Let every index have `N`-value at least the cutoff `a ≥ 0`, and
let `g` be nonincreasing on `[a, x]` with `0 ≤ g x`.  If the summatory function of a real weight `w`
is at most `C` at every cutoff in `[a, x]`, then the summatory function at `x` of the twisted weight
`i ↦ w i * g (N i)` is at most `C * g a`.

No sign condition is imposed on `w` or on `C`: only the partial sums of `w` are controlled. -/
theorem summatory_mul_le_of_summatory_le {a : ℝ} (ha : 0 ≤ a) (hN : ∀ i, a ≤ N i) (w : ι → ℝ)
    {g : ℝ → ℝ} {C x : ℝ} (hx : a ≤ x) (hC : ∀ t ∈ Set.Icc a x, summatory N w t ≤ C)
    (hg_diff : ∀ t ∈ Set.Icc a x, DifferentiableAt ℝ g t)
    (hg_int : IntegrableOn (deriv g) (Set.Icc a x))
    (hg_deriv : ∀ t ∈ Set.Icc a x, deriv g t ≤ 0) (hg_nonneg : 0 ≤ g x) :
    summatory N (fun i ↦ w i * g (N i)) x ≤ C * g a := by
  have key := summatory_mul_eq_sub_sub_integral_mul N w ha hx hg_diff hg_int
  rw [summatory_mul_eq_mul_summatory_of_le N hN w g] at key
  have hint : IntegrableOn (fun t ↦ deriv g t * summatory N w t) (Set.Ioc a x) :=
    (integrableOn_mul_summatory N w ha hg_int).mono_set Set.Ioc_subset_Icc_self
  have hmono : ∫ t in Set.Ioc a x, deriv g t * C ≤
      ∫ t in Set.Ioc a x, deriv g t * summatory N w t :=
    setIntegral_mono_on ((hg_int.mono_set Set.Ioc_subset_Icc_self).mul_const C) hint
      measurableSet_Ioc fun t ht ↦ mul_le_mul_of_nonpos_left
        (hC t (Set.Ioc_subset_Icc_self ht)) (hg_deriv t (Set.Ioc_subset_Icc_self ht))
  have hftc : ∫ t in Set.Ioc a x, deriv g t = g x - g a := by
    rw [← intervalIntegral.integral_of_le hx]
    exact intervalIntegral.integral_deriv_eq_sub
      (fun t ht ↦ hg_diff t (by rwa [Set.uIcc_of_le hx] at ht))
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hx).2 hg_int)
  rw [integral_mul_const, hftc] at hmono
  nlinarith [mul_le_mul_of_nonneg_left (hC x ⟨hx, le_rfl⟩) hg_nonneg]

/-- **A one-sided Abel bound for the full series.**  Let every index have `N`-value at least the
cutoff `a ≥ 0`.  If the summatory function of a real weight `w` is at most `C` at every cutoff
`t ≥ a`, and `g` is nonnegative and nonincreasing on `[a, ∞)`, then the sum of the summable twisted
family `i ↦ w i * g (N i)` is at most `C * g a`. -/
theorem tsum_mul_le_of_summatory_le {a : ℝ} (ha : 0 ≤ a) (hN : ∀ i, a ≤ N i) (w : ι → ℝ)
    {g : ℝ → ℝ} {C : ℝ} (hC : ∀ t, a ≤ t → summatory N w t ≤ C)
    (hg_diff : ∀ t, a ≤ t → DifferentiableAt ℝ g t)
    (hg_int : ∀ x, a ≤ x → IntegrableOn (deriv g) (Set.Icc a x))
    (hg_deriv : ∀ t, a ≤ t → deriv g t ≤ 0) (hg_nonneg : ∀ t, a ≤ t → 0 ≤ g t)
    (hsum : Summable fun i ↦ w i * g (N i)) :
    ∑' i, w i * g (N i) ≤ C * g a := by
  refine le_of_tendsto (hsum.hasSum.comp (tendsto_normLE_atTop N)) ?_
  filter_upwards [Filter.eventually_ge_atTop a] with x hx
  rw [Function.comp_apply, ← summatory_apply]
  exact summatory_mul_le_of_summatory_le N ha hN w hx (fun t ht ↦ hC t ht.1)
    (fun t ht ↦ hg_diff t ht.1) (hg_int x hx) (fun t ht ↦ hg_deriv t ht.1) (hg_nonneg x hx)

/-! ### The prime carrier of a number field -/

variable (K : Type*) [Field K] [NumberField K]

/-- Abel summation over the nonzero ideals of `𝓞 K`, from the cutoff `1`. -/
theorem idealSummatory_mul_eq_sub_integral_mul (w : (Ideal (𝓞 K))⁰ → 𝕜) {g : ℝ → 𝕜}
    (x : ℝ) (hg_diff : ∀ t ∈ Set.Icc 1 x, DifferentiableAt ℝ g t)
    (hg_int : IntegrableOn (deriv g) (Set.Icc 1 x)) :
    idealSummatory K (fun I ↦ w I * g (Ideal.absNorm (I : Ideal (𝓞 K)))) x =
      g x * idealSummatory K w x - ∫ t in Set.Ioc 1 x, deriv g t * idealSummatory K w t :=
  summatory_mul_eq_sub_integral_mul_of_one_le _ one_le_absNorm_real_of_nonZeroDivisors w x
    hg_diff hg_int

/-- An imaginary norm-power twist preserves a positive power bound for partial sums over the
nonzero ideals of a number field. -/
theorem norm_idealSummatory_mul_cpow_le_of_summatory_le
    (w : (Ideal (𝓞 K))⁰ → ℂ) {C θ x : ℝ} (hx : 1 ≤ x) (hθ : 0 < θ)
    (z : ℂ) (hz : z.re = 0)
    (hC : ∀ t, 1 ≤ t → ‖idealSummatory K w t‖ ≤ C * t ^ θ) :
    ‖idealSummatory K
      (fun I ↦ w I * (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-z)) x‖ ≤
        C * (1 + ‖z‖ / θ) * x ^ θ := by
  simpa only [idealSummatory] using
    norm_summatory_mul_cpow_le_of_summatory_le
      (fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K)))
      one_le_absNorm_real_of_nonZeroDivisors w hx hθ z hz hC

/-- Abel summation over the height-one primes of `𝓞 K`, from the cutoff `2`. -/
theorem primeSummatory_mul_eq_sub_integral_mul (w : HeightOneSpectrum (𝓞 K) → ℝ) {g : ℝ → ℝ}
    (x : ℝ) (hg_diff : ∀ t ∈ Set.Icc 2 x, DifferentiableAt ℝ g t)
    (hg_int : IntegrableOn (deriv g) (Set.Icc 2 x)) :
    primeSummatory K (fun v ↦ w v * g (Ideal.absNorm v.asIdeal)) x =
      g x * primeSummatory K w x - ∫ t in Set.Ioc 2 x, deriv g t * primeSummatory K w t :=
  summatory_mul_eq_sub_integral_mul_of_two_le _ two_le_absNorm_asIdeal_real w x hg_diff hg_int

variable {K}

private theorem primeTheta_eq_primeSummatory (S : Set (HeightOneSpectrum (𝓞 K))) (x : ℝ) :
    primeTheta K S x =
      primeSummatory K (S.indicator fun v ↦ Real.log (Ideal.absNorm v.asIdeal : ℝ)) x := by
  rw [primeTheta_apply, primeSummatory_apply]

private theorem primeCount_eq_primeSummatory (S : Set (HeightOneSpectrum (𝓞 K))) (x : ℝ) :
    primeCount K S x = primeSummatory K (S.indicator 1) x := by
  rw [primeCount_apply, primeSummatory_apply]

/-- **Chebyshev's `ϑ` from `π`.**  The logarithmically weighted prime count is recovered from the
unweighted one by Abel summation, with the inclusive cutoff and the half-open integration range
fixed by the roadmap's conventions. -/
theorem primeTheta_eq_log_mul_primeCount_sub_integral (S : Set (HeightOneSpectrum (𝓞 K)))
    (x : ℝ) :
    primeTheta K S x =
      Real.log x * primeCount K S x - ∫ t in Set.Ioc 2 x, primeCount K S t / t := by
  have hw : (fun v : HeightOneSpectrum (𝓞 K) ↦ S.indicator (1 : HeightOneSpectrum (𝓞 K) → ℝ) v *
      Real.log (Ideal.absNorm v.asIdeal : ℝ)) =
      S.indicator fun v ↦ Real.log (Ideal.absNorm v.asIdeal : ℝ) := by
    funext v
    by_cases hv : v ∈ S
    · rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv, Pi.one_apply, one_mul]
    · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv, zero_mul]
  have hdiff : ∀ t ∈ Set.Icc (2 : ℝ) x, DifferentiableAt ℝ Real.log t := fun t ht ↦
    Real.differentiableAt_log (by linarith [ht.1] : (0 : ℝ) < t).ne'
  have hint : IntegrableOn (deriv Real.log) (Set.Icc (2 : ℝ) x) := by
    rw [Real.deriv_log']
    refine ContinuousOn.integrableOn_Icc (continuousOn_inv₀.mono fun t ht ↦ ?_)
    simpa using (by linarith [ht.1] : (0 : ℝ) < t).ne'
  have key : primeTheta K S x = Real.log x * primeCount K S x -
      ∫ t in Set.Ioc (2 : ℝ) x, deriv Real.log t * primeCount K S t := by
    simp only [primeTheta_eq_primeSummatory, primeCount_eq_primeSummatory]
    rw [← hw]
    exact primeSummatory_mul_eq_sub_integral_mul K _ x hdiff hint
  have hI : ∫ t in Set.Ioc (2 : ℝ) x, deriv Real.log t * primeCount K S t =
      ∫ t in Set.Ioc (2 : ℝ) x, primeCount K S t / t :=
    setIntegral_congr_fun measurableSet_Ioc fun t _ ↦ by rw [Real.deriv_log, inv_mul_eq_div]
  rw [key, hI]

/-- **Chebyshev's `π` from `ϑ`.**  The unweighted prime count is recovered from the logarithmically
weighted one by Abel summation.  This is the finite identity whose two terms Layer 6.2 estimates
in order to turn `ϑ(x) ∼ δx` into `π(x) ∼ δ Li(x)`. -/
theorem primeCount_eq_primeTheta_div_log_add_integral (S : Set (HeightOneSpectrum (𝓞 K)))
    (x : ℝ) :
    primeCount K S x = primeTheta K S x / Real.log x +
      ∫ t in Set.Ioc 2 x, primeTheta K S t / (t * Real.log t ^ 2) := by
  have hw : (fun v : HeightOneSpectrum (𝓞 K) ↦
      S.indicator (fun v ↦ Real.log (Ideal.absNorm v.asIdeal : ℝ)) v *
        (Real.log (Ideal.absNorm v.asIdeal : ℝ))⁻¹) =
      S.indicator (1 : HeightOneSpectrum (𝓞 K) → ℝ) := by
    funext v
    by_cases hv : v ∈ S
    · rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv, Pi.one_apply,
        mul_inv_cancel₀ (log_absNorm_asIdeal_pos v).ne']
    · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv, zero_mul]
  have hdiff : ∀ t ∈ Set.Icc (2 : ℝ) x, DifferentiableAt ℝ (fun u : ℝ ↦ (Real.log u)⁻¹) t :=
    fun t ht ↦ Real.differentiableAt_inv_log (by linarith [ht.1] : (0 : ℝ) < t).ne'
      (by linarith [ht.1] : (1 : ℝ) < t).ne' (by linarith [ht.1] : (-1 : ℝ) < t).ne'
  have hint : IntegrableOn (deriv fun u : ℝ ↦ (Real.log u)⁻¹) (Set.Icc (2 : ℝ) x) := by
    rw [Real.deriv_inv_log]
    refine ContinuousOn.integrableOn_Icc fun t ht ↦ ?_
    have ht0 : t ≠ 0 := (by linarith [ht.1] : (0 : ℝ) < t).ne'
    exact (((continuousAt_id.inv₀ ht0).neg).div ((Real.continuousAt_log ht0).pow 2)
      (pow_ne_zero 2 (Real.log_pos (by linarith [ht.1])).ne')).continuousWithinAt
  have key : primeCount K S x = (Real.log x)⁻¹ * primeTheta K S x -
      ∫ t in Set.Ioc (2 : ℝ) x, deriv (fun u : ℝ ↦ (Real.log u)⁻¹) t * primeTheta K S t := by
    simp only [primeCount_eq_primeSummatory, primeTheta_eq_primeSummatory]
    rw [← hw]
    exact primeSummatory_mul_eq_sub_integral_mul K _ x hdiff hint
  have hI : ∫ t in Set.Ioc (2 : ℝ) x, deriv (fun u : ℝ ↦ (Real.log u)⁻¹) t * primeTheta K S t =
      -∫ t in Set.Ioc (2 : ℝ) x, primeTheta K S t / (t * Real.log t ^ 2) := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht ↦ ?_
    have ht0 : t ≠ 0 := (by linarith [ht.1] : (0 : ℝ) < t).ne'
    have hlog : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    rw [Real.deriv_inv_log_apply]
    field_simp
  rw [key, hI]
  ring

end TauCeti
