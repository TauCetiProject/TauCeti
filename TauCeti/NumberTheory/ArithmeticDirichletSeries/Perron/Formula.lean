/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Perron.Basic
public import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The arithmetic Perron formula

`TauCeti.truncatedPerronKernel` is the Perron kernel of a single ratio `x`.  This file applies it
to an absolutely convergent `L`-series: the integral over the truncated segment of the series
against the Perron integrand is the series of the individual kernels, one for each `x / n`.

## Main results

* `TauCeti.integral_LSeries_mul_perronIntegrand`: the interchange of the integral with the series.
* `TauCeti.truncatedPerron_LSeries`: the truncated summatory formula, as a series of truncated
  Perron kernels at the ratios `x / n`.
* `TauCeti.norm_truncatedPerron_LSeries_sub_sum_le`: the off-norm form, comparing the truncated
  integral with the sharp partial sum `∑_{n < x} f n`.
* `TauCeti.tendsto_truncatedPerron_LSeries`: the limiting form, at every positive `x`.
* `TauCeti.tsum_mul_perronStep_natCast`: the limit at an integer endpoint, where the endpoint
  enters with the customary half weight `f N / 2`.
* `TauCeti.tendsto_truncatedPerron_LSeries_natCast`: that limit read off directly, as the finite
  sum below `N` together with `f N / 2`.

## References

* H. Davenport, *Multiplicative Number Theory*, chapter 17, for Perron's formula and the
  half weight at an integer endpoint.
-/

public section

namespace TauCeti

open Complex Filter MeasureTheory Topology

open scoped ENNReal Real

variable {f : ℕ → ℂ} {x c T : ℝ}

private theorem norm_term_mul_perronIntegrand_le (hx : 0 < x) (hc : 0 < c) (n : ℕ) (t : ℝ) :
    ‖LSeries.term f ((c : ℂ) + t * I) n * perronIntegrand x c t‖ ≤
      ‖LSeries.term f (c : ℂ) n‖ * (x ^ c / Real.sqrt (c ^ 2 + t ^ 2)) := by
  rw [norm_mul, norm_perronIntegrand hx]
  gcongr
  exact LSeries.norm_term_le_of_re_le_re f (by simp) n

/-- The termwise lower integrals of `‖term f (c + i t) n * perronIntegrand x c t‖` over the
truncated segment have finite total sum, where the `L`-series converges absolutely on the line
`Re s = c`.  This is the `L¹` hypothesis of `MeasureTheory.integral_tsum`. -/
private theorem lintegral_norm_term_mul_perronIntegrand_ne_top (hx : 0 < x) (hc : 0 < c)
    (h : LSeriesSummable f (c : ℂ)) :
    ∑' n : ℕ, ∫⁻ t in Set.Ioc (-T) T,
        ‖LSeries.term f ((c : ℂ) + t * I) n * perronIntegrand x c t‖ₑ ≠ ∞ := by
  have hstep : ∀ n : ℕ, ∫⁻ t in Set.Ioc (-T) T,
      ‖LSeries.term f ((c : ℂ) + t * I) n * perronIntegrand x c t‖ₑ ≤
        ENNReal.ofReal (‖LSeries.term f (c : ℂ) n‖ * (x ^ c / c)) * ENNReal.ofReal (2 * T) := by
    intro n
    have hbd : ∀ t : ℝ, ‖LSeries.term f ((c : ℂ) + t * I) n * perronIntegrand x c t‖ₑ ≤
        ENNReal.ofReal (‖LSeries.term f (c : ℂ) n‖ * (x ^ c / c)) := by
      intro t
      rw [← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ((norm_term_mul_perronIntegrand_le hx hc n t).trans ?_)
      have hge : c ≤ Real.sqrt (c ^ 2 + t ^ 2) :=
        (Real.sqrt_sq hc.le).ge.trans (Real.sqrt_le_sqrt (by nlinarith [sq_nonneg t]))
      have hxc : (0 : ℝ) ≤ x ^ c := Real.rpow_nonneg hx.le c
      gcongr
    calc ∫⁻ t in Set.Ioc (-T) T, ‖LSeries.term f ((c : ℂ) + t * I) n * perronIntegrand x c t‖ₑ
        ≤ ∫⁻ _ in Set.Ioc (-T) T,
            ENNReal.ofReal (‖LSeries.term f (c : ℂ) n‖ * (x ^ c / c)) := lintegral_mono hbd
      _ = ENNReal.ofReal (‖LSeries.term f (c : ℂ) n‖ * (x ^ c / c)) * ENNReal.ofReal (2 * T) := by
          have hlen : T - -T = 2 * T := by ring
          rw [setLIntegral_const, Real.volume_Ioc, hlen]
  refine ne_of_lt (lt_of_le_of_lt (ENNReal.tsum_le_tsum hstep) ?_)
  rw [ENNReal.tsum_mul_right]
  refine ENNReal.mul_lt_top ?_ ENNReal.ofReal_lt_top
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n ↦ by positivity) (h.norm.mul_right _)]
  exact ENNReal.ofReal_lt_top

/-- Each `L`-series term is continuous in the height along the line `Re s = c`. -/
private theorem continuous_term_line (f : ℕ → ℂ) (c : ℝ) (n : ℕ) :
    Continuous fun t : ℝ ↦ LSeries.term f ((c : ℂ) + t * I) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simpa using continuous_const
  · have hline : Continuous fun t : ℝ ↦ (c : ℂ) + t * I :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
    simp only [LSeries.term_of_ne_zero hn]
    refine continuous_const.div (hline.const_cpow (Or.inl hn0)) fun t ↦ ?_
    exact fun h ↦ hn0 ((Complex.cpow_eq_zero_iff _ _).mp h).1

/-- **The interchange.**  Where the `L`-series converges absolutely on the line `Re s = c`, the
integral over the truncated segment of the series times the Perron integrand is the series of the
integrals. -/
theorem integral_LSeries_mul_perronIntegrand (hx : 0 < x) (hc : 0 < c)
    (h : LSeriesSummable f (c : ℂ)) :
    ∫ t in Set.Ioc (-T) T, (∑' n : ℕ, LSeries.term f ((c : ℂ) + t * I) n) * perronIntegrand x c t
      = ∑' n : ℕ, ∫ t in Set.Ioc (-T) T,
          LSeries.term f ((c : ℂ) + t * I) n * perronIntegrand x c t := by
  rw [← MeasureTheory.integral_tsum (fun n ↦ ?_) (lintegral_norm_term_mul_perronIntegrand_ne_top
    hx hc h)]
  · exact integral_congr_ae (.of_forall fun t ↦ tsum_mul_right.symm)
  · exact ((continuous_term_line f c n).mul
      (continuous_perronIntegrand hx.ne' hc.ne')).aestronglyMeasurable

/-- **Collecting a term into the integrand.**  The `n`-th `L`-series term against the Perron
integrand at `x` is the coefficient `f n` against the Perron integrand at the ratio `x / n`. -/
theorem term_mul_perronIntegrand (hx : 0 ≤ x) (hc : c ≠ 0) (n : ℕ) (t : ℝ) :
    LSeries.term f ((c : ℂ) + t * I) n * perronIntegrand x c t =
      f n * perronIntegrand (x / n) c t := by
  have hline : (c : ℂ) + t * I ≠ 0 := fun h ↦ hc (by simpa using congrArg Complex.re h)
  rcases eq_or_ne n 0 with rfl | hn
  · rw [LSeries.term_zero, zero_mul, Nat.cast_zero, div_zero, perronIntegrand_def,
      Complex.ofReal_zero, Complex.zero_cpow hline, zero_div, mul_zero]
  · rw [LSeries.term_of_ne_zero hn, perronIntegrand_def, perronIntegrand_def,
      Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg hx (Nat.cast_nonneg n),
      Complex.ofReal_natCast]
    ring

/-- **The truncated Perron formula for an `L`-series.**  Where the series converges absolutely on
the line `Re s = c`, the truncated Perron integral of the series is the series of the truncated
Perron kernels at the ratios `x / n`. -/
theorem truncatedPerron_LSeries (hx : 0 < x) (hc : 0 < c) (hT : 0 ≤ T)
    (h : LSeriesSummable f (c : ℂ)) :
    ((2 * π : ℝ) : ℂ)⁻¹ * ∫ t in -T..T, LSeries f ((c : ℂ) + t * I) * perronIntegrand x c t
      = ∑' n : ℕ, f n * truncatedPerronKernel (x / n) c T := by
  have hle : -T ≤ T := by linarith
  -- Mathlib exports no equation lemma for `LSeries`, so its defining equation is named here
  -- rather than left to unfold silently inside the rewrite below.
  have hLSeries : ∀ t : ℝ,
      LSeries f ((c : ℂ) + t * I) = ∑' n : ℕ, LSeries.term f ((c : ℂ) + t * I) n := fun _ ↦ rfl
  rw [intervalIntegral.integral_of_le hle]
  simp only [hLSeries]
  rw [integral_LSeries_mul_perronIntegrand hx hc h, ← tsum_mul_left]
  refine tsum_congr fun n ↦ ?_
  rw [truncatedPerronKernel_def, intervalIntegral.integral_of_le hle,
    integral_congr_ae (.of_forall fun t ↦ term_mul_perronIntegrand hx.le hc.ne' n t),
    MeasureTheory.integral_const_mul]
  ring

/-- Off the norms the step weight kills every index outside `Finset.Ico 1 ⌈x⌉₊`: the index `0`
because `x / 0` is `0`, and an index at or above `⌈x⌉₊` because there `x / n < 1`. -/
private theorem mul_perronStep_div_eq_zero_of_notMem (hoff : ∀ n : ℕ, x ≠ n) (f : ℕ → ℂ) {n : ℕ}
    (hn : n ∉ Finset.Ico 1 ⌈x⌉₊) : f n * perronStep (x / n) = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · rw [Nat.cast_zero, div_zero, perronStep_of_lt_one zero_lt_one, mul_zero]
  · have hge : ⌈x⌉₊ ≤ n := by
      simp only [Finset.mem_Ico, not_and, not_lt] at hn
      exact hn hn0
    have hcast : (0 : ℝ) < n := Nat.cast_pos.2 hn0
    have hxn : x < n := lt_of_le_of_ne (Nat.ceil_le.1 hge) (hoff n)
    rw [perronStep_of_lt_one ((div_lt_one hcast).2 hxn), mul_zero]

/-- **The Perron step series is a sharp partial sum.**  When `x` is not a natural number the step
weights are `1` at the indices below `x` and `0` at those above it, so only `n < x` contributes. -/
theorem tsum_mul_perronStep_div (hoff : ∀ n : ℕ, x ≠ n) (f : ℕ → ℂ) :
    ∑' n : ℕ, f n * perronStep (x / n) = ∑ n ∈ Finset.Ico 1 ⌈x⌉₊, f n := by
  rw [tsum_eq_sum fun n hn ↦ mul_perronStep_div_eq_zero_of_notMem hoff f hn]
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  simp only [Finset.mem_Ico] at hn
  have hcast : (0 : ℝ) < n := Nat.cast_pos.2 hn.1
  rw [perronStep_of_one_lt ((one_lt_div hcast).2 (Nat.lt_ceil.1 hn.2)), mul_one]

/-- Beyond `2 x` the ratio `x / n` is at most `1 / 2`, so `|log (x / n)|` is bounded below by
`log 2` and the smoothed-step error at index `n` is a fixed multiple of `‖LSeries.term f c n‖`.
Absolute convergence of the `L`-series on the line therefore makes the error series summable. -/
private theorem summable_norm_mul_kernelError (hx : 0 < x) (hT : 0 < T)
    (h : LSeriesSummable f (c : ℂ)) :
    Summable fun n : ℕ ↦ ‖f n‖ * ((x / n) ^ c / (π * T * |Real.log (x / n)|)) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hg : Summable fun n : ℕ ↦ x ^ c / (π * T * Real.log 2) * ‖LSeries.term f (c : ℂ) n‖ :=
    (summable_norm_iff.2 h).mul_left _
  refine Summable.of_norm_bounded_eventually_nat hg ?_
  filter_upwards [Filter.eventually_ge_atTop ⌈2 * x⌉₊, Filter.eventually_gt_atTop 0] with n hn hn0
  have hcast : (0 : ℝ) < n := Nat.cast_pos.2 hn0
  have hle : 2 * x ≤ n := Nat.ceil_le.1 hn
  have hxn : 0 < x / n := div_pos hx hcast
  have hhalf : x / n ≤ 1 / 2 := by rw [div_le_iff₀ hcast]; linarith
  have hlog : Real.log 2 ≤ |Real.log (x / n)| := by
    have hmono : Real.log (x / n) ≤ Real.log (1 / 2) := Real.log_le_log hxn hhalf
    rw [Real.log_div one_ne_zero two_ne_zero, Real.log_one, zero_sub] at hmono
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hnorm : ‖LSeries.term f (c : ℂ) n‖ = ‖f n‖ / n ^ c := by
    rw [LSeries.norm_term_eq]
    simp [hn0.ne']
  rw [Real.norm_of_nonneg (by positivity), hnorm, Real.div_rpow hx.le hcast.le]
  have hbound : ‖f n‖ * (x ^ c / n ^ c / (π * T * |Real.log (x / n)|))
      ≤ ‖f n‖ * (x ^ c / n ^ c / (π * T * Real.log 2)) := by
    gcongr
  exact hbound.trans_eq (by ring)

/-- At each index the `n`-th term of the truncated Perron series differs from its sharp step by at
most `‖f n‖` times the smoothed-step kernel error at the ratio `x / n`.  The index `0`
contributes
nothing on either side. -/
private theorem norm_mul_truncatedPerronKernel_sub_step_le (hx : 0 < x) (hc : 0 < c) (hT : 0 < T)
    (hoff : ∀ n : ℕ, x ≠ n) (f : ℕ → ℂ) (n : ℕ) :
    ‖f n * truncatedPerronKernel (x / n) c T - f n * perronStep (x / n)‖
      ≤ ‖f n‖ * ((x / n) ^ c / (π * T * |Real.log (x / n)|)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · rw [Nat.cast_zero, div_zero, truncatedPerronKernel_zero hc.ne', mul_zero,
      perronStep_of_lt_one zero_lt_one, mul_zero, sub_zero, norm_zero]
    positivity
  · have hcast : (0 : ℝ) < n := Nat.cast_pos.2 hn0
    have hne : x / n ≠ 1 := fun hh ↦ hoff n ((div_eq_one_iff_eq hcast.ne').1 hh)
    rw [← mul_sub, norm_mul]
    gcongr
    exact norm_truncatedPerronKernel_sub_step_le (div_pos hx hcast) hne hc hT

/-- **The off-norm arithmetic Perron formula.**  When `x` is not a natural number the truncated
integral differs from the sharp partial sum `∑_{n < x} f n` by at most the series of the
smoothed-step kernel errors, a series that absolute convergence on the line makes summable. -/
theorem norm_truncatedPerron_LSeries_sub_sum_le (hx : 0 < x) (hc : 0 < c) (hT : 0 < T)
    (hoff : ∀ n : ℕ, x ≠ n) (h : LSeriesSummable f (c : ℂ)) :
    ‖(((2 * π : ℝ) : ℂ)⁻¹ * ∫ t in -T..T, LSeries f ((c : ℂ) + t * I) * perronIntegrand x c t)
        - ∑ n ∈ Finset.Ico 1 ⌈x⌉₊, f n‖
      ≤ ∑' n : ℕ, ‖f n‖ * ((x / n) ^ c / (π * T * |Real.log (x / n)|)) := by
  have herr := summable_norm_mul_kernelError hx hT h
  have hstep := norm_mul_truncatedPerronKernel_sub_step_le hx hc hT hoff f
  have hDnorm : Summable fun n : ℕ ↦
      ‖f n * truncatedPerronKernel (x / n) c T - f n * perronStep (x / n)‖ :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hstep herr
  have hD : Summable fun n : ℕ ↦
      f n * truncatedPerronKernel (x / n) c T - f n * perronStep (x / n) := .of_norm hDnorm
  have hB : Summable fun n : ℕ ↦ f n * perronStep (x / n) :=
    summable_of_ne_finset_zero (s := Finset.Ico 1 ⌈x⌉₊) fun n hn ↦
      mul_perronStep_div_eq_zero_of_notMem hoff f hn
  have hA : Summable fun n : ℕ ↦ f n * truncatedPerronKernel (x / n) c T := by
    simpa using hD.add hB
  rw [truncatedPerron_LSeries hx hc hT.le h, ← tsum_mul_perronStep_div hoff f,
    ← hA.tsum_sub hB]
  exact (norm_tsum_le_tsum_norm hDnorm).trans (Summable.tsum_le_tsum hstep hDnorm herr)

/-- Uniformly in heights `T ≥ 1`, the truncated Perron kernel at a positive ratio `y` is bounded by
the smoothed-step error at `y`, together with `1` once `y` exceeds `1 / 2`.  Above `1 / 2` the sharp
step may be nonzero and contributes that `1`; below it the step vanishes and the error alone
suffices, and at the excluded ratio `y = 1` the kernel is `π⁻¹ arctan (T / c)`. -/
private theorem norm_truncatedPerronKernel_le_bound (hy : 0 < y) (hc : 0 < c) (hT : 1 ≤ T) :
    ‖truncatedPerronKernel y c T‖
      ≤ y ^ c / (π * 1 * |Real.log y|) + (if 1 / 2 < y then 1 else 0) := by
  rcases eq_or_ne y 1 with rfl | hne
  · have hif : (if (1 : ℝ) / 2 < (1 : ℝ) then (1 : ℝ) else 0) = 1 := by norm_num
    rw [hif]
    have : (0 : ℝ) ≤ (1 : ℝ) ^ c / (π * 1 * |Real.log 1|) := by positivity
    linarith [norm_truncatedPerronKernel_one_le (c := c) hc.ne' T]
  have hlog : 0 < |Real.log y| := abs_pos.2 (Real.log_ne_zero_of_pos_of_ne_one hy hne)
  have herr : ‖truncatedPerronKernel y c T - perronStep y‖ ≤ y ^ c / (π * 1 * |Real.log y|) := by
    refine (norm_truncatedPerronKernel_sub_step_le hy hne hc (by linarith)).trans ?_
    gcongr
  split_ifs with hhalf
  · have htri := norm_add_le (truncatedPerronKernel y c T - perronStep y) (perronStep y)
    rw [sub_add_cancel] at htri
    exact htri.trans (by gcongr; exact norm_perronStep_le_one _)
  · push Not at hhalf
    have hy1 : y < 1 := by linarith
    rw [add_zero, ← sub_zero (truncatedPerronKernel y c T),
      ← perronStep_of_lt_one hy1]
    exact herr

/-- Only the indices below `2 x` have ratio `x / n` above `1 / 2`, so a term supported there is a
finite sum and trivially summable. -/
private theorem summable_indicator_norm_of_half_lt (hx : 0 < x) (f : ℕ → ℂ) :
    Summable fun n : ℕ ↦ (if 1 / 2 < x / n then ‖f n‖ else 0) :=
  summable_of_ne_finset_zero (s := Finset.range ⌈2 * x⌉₊) fun n hn ↦ by
    simp only [Finset.mem_range, not_lt] at hn
    have hcast : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) (Nat.ceil_le.1 hn)
    have hle : x / n ≤ 1 / 2 := by rw [div_le_iff₀ hcast]; linarith [Nat.ceil_le.1 hn]
    exact ite_eq_right_iff.2 fun hc ↦ absurd hc (not_lt.2 hle)

/-- **The limiting arithmetic Perron formula.**  As the truncation height grows the integral tends
to the series of sharp steps `∑' n, f n * perronStep (x / n)`.  This holds at every positive `x`,
integer endpoints included; `TauCeti.tsum_mul_perronStep_natCast` evaluates the limit there. -/
theorem tendsto_truncatedPerron_LSeries (hx : 0 < x) (hc : 0 < c)
    (h : LSeriesSummable f (c : ℂ)) :
    Tendsto (fun T : ℝ ↦ ((2 * π : ℝ) : ℂ)⁻¹ *
        ∫ t in -T..T, LSeries f ((c : ℂ) + t * I) * perronIntegrand x c t) atTop
      (𝓝 (∑' n : ℕ, f n * perronStep (x / n))) := by
  have hfin := summable_indicator_norm_of_half_lt hx f
  have hpt : ∀ n : ℕ, Tendsto (fun T : ℝ ↦ f n * truncatedPerronKernel (x / n) c T) atTop
      (𝓝 (f n * perronStep (x / n))) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp only [Nat.cast_zero, div_zero, truncatedPerronKernel_zero hc.ne', mul_zero,
        perronStep_of_lt_one zero_lt_one]
      exact tendsto_const_nhds
    · exact ((tendsto_truncatedPerronKernel (div_pos hx (Nat.cast_pos.2 hn0)) hc).const_mul _)
  have hdom : ∀ᶠ T : ℝ in atTop, ∀ n : ℕ,
      ‖f n * truncatedPerronKernel (x / n) c T‖ ≤
        ‖f n‖ * ((x / n) ^ c / (π * 1 * |Real.log (x / n)|)) +
          (if 1 / 2 < x / n then ‖f n‖ else 0) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT n
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · rw [Nat.cast_zero, div_zero, truncatedPerronKernel_zero hc.ne', mul_zero, norm_zero]
      split_ifs <;> positivity
    · rw [norm_mul]
      have hbd := norm_truncatedPerronKernel_le_bound (div_pos hx (Nat.cast_pos.2 hn0)) hc hT
      split_ifs at hbd ⊢ with hhalf
      · nlinarith [norm_nonneg (f n), norm_nonneg (truncatedPerronKernel (x / n) c T)]
      · nlinarith [norm_nonneg (f n), norm_nonneg (truncatedPerronKernel (x / n) c T)]
  refine Tendsto.congr' ?_
    (tendsto_tsum_of_dominated_convergence
      ((summable_norm_mul_kernelError hx one_pos h).add hfin) hpt hdom)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  exact (truncatedPerron_LSeries hx hc hT h).symm

/-- **The half weight at an integer endpoint.**  At `x = N` the step series is the partial sum
below `N` together with the customary half of the endpoint term. -/
theorem tsum_mul_perronStep_natCast {N : ℕ} (hN : 0 < N) (f : ℕ → ℂ) :
    ∑' n : ℕ, f n * perronStep ((N : ℝ) / n) = (∑ n ∈ Finset.Ico 1 N, f n) + f N / 2 := by
  have hzero : ∀ n ∉ Finset.Ico 1 (N + 1), f n * perronStep ((N : ℝ) / n) = 0 := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · rw [Nat.cast_zero, div_zero, perronStep_of_lt_one zero_lt_one, mul_zero]
    · have hgt : N < n := by
        simp only [Finset.mem_Ico, not_and, not_lt, Nat.succ_le_iff] at hn
        exact hn hn0
      have hcast : (0 : ℝ) < n := Nat.cast_pos.2 hn0
      have : (N : ℝ) < n := Nat.cast_lt.2 hgt
      rw [perronStep_of_lt_one ((div_lt_one hcast).2 this), mul_zero]
  rw [tsum_eq_sum hzero, Finset.sum_Ico_succ_top hN]
  have hNcast : (0 : ℝ) < N := Nat.cast_pos.2 hN
  rw [div_self hNcast.ne', perronStep_one]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun n hn ↦ ?_) (by ring)
  simp only [Finset.mem_Ico] at hn
  have hcast : (0 : ℝ) < n := Nat.cast_pos.2 hn.1
  rw [perronStep_of_one_lt ((one_lt_div hcast).2 (Nat.cast_lt.2 hn.2)), mul_one]

/-- **The arithmetic Perron formula at an integer endpoint.**  At `x = N` the truncated integral
tends to the sum of `f` below `N` together with half of the endpoint term. -/
theorem tendsto_truncatedPerron_LSeries_natCast {N : ℕ} (hN : 0 < N) (hc : 0 < c)
    (h : LSeriesSummable f (c : ℂ)) :
    Tendsto (fun T : ℝ ↦ ((2 * π : ℝ) : ℂ)⁻¹ *
        ∫ t in -T..T, LSeries f ((c : ℂ) + t * I) * perronIntegrand N c t) atTop
      (𝓝 ((∑ n ∈ Finset.Ico 1 N, f n) + f N / 2)) := by
  have hx : (0 : ℝ) < N := Nat.cast_pos.2 hN
  rw [← tsum_mul_perronStep_natCast hN f]
  exact tendsto_truncatedPerron_LSeries hx hc h

end TauCeti
