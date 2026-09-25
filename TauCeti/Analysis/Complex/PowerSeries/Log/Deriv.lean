/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.OfScalars
public import TauCeti.RingTheory.PowerSeries.Log
public import Mathlib.Analysis.Complex.TaylorSeries

/-!
# Convergence of formal logarithmic derivatives

This file connects the formal logarithmic derivative of a complex power series to its analytic
sum. If a power series has constant coefficient one and its analytic sum has no zero in a disk
of convergence, then its formal logarithmic derivative converges throughout that disk.

The zero-free hypothesis is essential: the radius of the logarithmic derivative is limited by the
nearest zero of the original series, even when the original series converges farther.
Quantitatively, if the coefficients of `f - 1` have absolute sum less than one on a circle, the
file gives an explicit bound for the absolute coefficient sum of `f'/f` there.

## Main results

* `PowerSeries.hasSum_coeff_logDeriv_mul_pow_of_zeroFree`: evaluation of the formal
  logarithmic derivative throughout a zero-free convergence disk.
* `PowerSeries.summable_norm_coeff_logDeriv_mul_pow_of_zeroFree`: absolute convergence of the
  formal logarithmic derivative throughout a zero-free convergence disk.
* `PowerSeries.tsum_norm_coeff_logDeriv_mul_pow_succ_le`: an explicit bound for the absolute
  coefficient sum of the formal logarithmic derivative when `f` is close to `1`.
-/

public section

namespace PowerSeries

open Filter
open scoped Topology

private theorem coeff_logDeriv_recurrence (f : ℂ⟦X⟧) (hf0 : constantCoeff f = 1) (m : ℕ) :
    ∑ i ∈ Finset.range (m + 1), coeff i (logDeriv f) * coeff (m - i) f =
      (m + 1) * coeff (m + 1) f := by
  have hformal := congrArg (coeff m) (logDeriv_mul f hf0)
  rw [coeff_mul, coeff_derivative] at hformal
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j ↦ coeff i (logDeriv f) * coeff j f)] at hformal
  simpa [mul_comm] using hformal

private theorem iteratedDeriv_logDeriv_recurrence (f : ℂ⟦X⟧)
    (hf0 : constantCoeff f = 1)
    (hf : 0 < (FormalMultilinearSeries.ofScalars ℂ fun n ↦ coeff n f).radius) (m : ℕ) :
    ∑ i ∈ Finset.range (m + 1),
        (iteratedDeriv i
          (_root_.logDeriv
            (FormalMultilinearSeries.ofScalarsSum (E := ℂ) fun n ↦ coeff n f)) 0 /
            i.factorial) * coeff (m - i) f =
      (m + 1) * coeff (m + 1) f := by
  let F := FormalMultilinearSeries.ofScalarsSum (E := ℂ) fun n ↦ coeff n f
  let G := _root_.logDeriv F
  have hFa : AnalyticAt ℂ F 0 :=
    ((FormalMultilinearSeries.ofScalars ℂ fun n ↦ coeff n f).hasFPowerSeriesOnBall hf)
      |>.analyticAt_of_mem (Metric.mem_eball_self hf)
  have hFderiv (k : ℕ) : iteratedDeriv k F 0 = k.factorial * coeff k f := by
    simpa [F] using FormalMultilinearSeries.iteratedDeriv_ofScalarsSum_zero
      (fun n ↦ coeff n f) hf k
  have hF0 : F 0 = 1 := by
    calc
      F 0 = coeff 0 f := by
        dsimp [F]
        simp [FormalMultilinearSeries.ofScalarsSum_zero]
      _ = 1 := by simpa [constantCoeff] using hf0
  have hGa : AnalyticAt ℂ G 0 := hFa.deriv.div hFa (by rw [hF0]; exact one_ne_zero)
  have hmul : G * F =ᶠ[𝓝 (0 : ℂ)] deriv F := by
    filter_upwards [hFa.continuousAt.eventually_ne (by rw [hF0]; exact one_ne_zero)] with z hz
    simp [G, logDeriv_apply, hz]
  have hderivEq : iteratedDeriv m (G * F) 0 = iteratedDeriv m (deriv F) 0 :=
    hmul.iteratedDeriv_eq m
  rw [iteratedDeriv_mul hGa.contDiffAt hFa.contDiffAt, ← iteratedDeriv_succ'] at hderivEq
  simp_rw [hFderiv] at hderivEq
  have hnfac : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  apply (mul_left_cancel₀ hnfac)
  calc
    (m.factorial : ℂ) *
        ∑ i ∈ Finset.range (m + 1),
          (iteratedDeriv i G 0 / i.factorial) * coeff (m - i) f =
        ∑ i ∈ Finset.range (m + 1),
          m.choose i * iteratedDeriv i G 0 * ((m - i).factorial * coeff (m - i) f) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          have hin : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
          have hfac : m.choose i * i.factorial * (m - i).factorial = m.factorial :=
            Nat.choose_mul_factorial_mul_factorial hin
          have hfac' : (m.choose i : ℂ) * (i.factorial : ℂ) *
              ((m - i).factorial : ℂ) = (m.factorial : ℂ) := by exact_mod_cast hfac
          have hi0 : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
          rw [← hfac']
          field_simp [hi0]
    _ = ((m + 1).factorial : ℂ) * coeff (m + 1) f := hderivEq
    _ = (m.factorial : ℂ) * ((m + 1) * coeff (m + 1) f) := by
      push_cast [Nat.factorial_succ]
      ring

/-- The coefficients of a formal logarithmic derivative are the normalized iterated derivatives
at zero of the analytic logarithmic derivative. -/
theorem coeff_logDeriv_eq_iteratedDeriv (f : ℂ⟦X⟧)
    (hf0 : constantCoeff f = 1)
    (hf : 0 < (FormalMultilinearSeries.ofScalars ℂ fun n ↦ coeff n f).radius) (n : ℕ) :
    coeff n (logDeriv f) =
      iteratedDeriv n
        (_root_.logDeriv
          (FormalMultilinearSeries.ofScalarsSum (E := ℂ) fun n ↦ coeff n f)) 0 /
          n.factorial := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hr := coeff_logDeriv_recurrence f hf0 n
      have ha := iteratedDeriv_logDeriv_recurrence f hf0 hf n
      rw [Finset.sum_range_succ] at hr ha
      have hlower :
          ∑ i ∈ Finset.range n, coeff i (logDeriv f) * coeff (n - i) f =
            ∑ i ∈ Finset.range n,
              (iteratedDeriv i
                (_root_.logDeriv
                  (FormalMultilinearSeries.ofScalarsSum (E := ℂ) fun n ↦ coeff n f)) 0 /
                  i.factorial) *
                coeff (n - i) f := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [ih i (Finset.mem_range.mp hi)]
      have hfcoeff : coeff 0 f = 1 := by simpa [constantCoeff] using hf0
      rw [hlower, Nat.sub_self, hfcoeff, mul_one] at hr
      rw [Nat.sub_self, hfcoeff, mul_one] at ha
      exact add_left_cancel (hr.trans ha.symm)

private theorem hasFPowerSeriesOnBall_logDeriv_of_zeroFree (f : ℂ⟦X⟧)
    (hf0 : constantCoeff f = 1) {r : ENNReal} {R : NNReal}
    (hr : r ≤ (FormalMultilinearSeries.ofScalars ℂ fun n ↦ coeff n f).radius)
    (hne : ∀ z : ℂ, ‖z‖ₑ < r →
      FormalMultilinearSeries.ofScalarsSum (E := ℂ) (fun n ↦ coeff n f) z ≠ 0)
    (hR0 : 0 < R) (hRr : (R : ENNReal) < r) :
    HasFPowerSeriesOnBall
      (_root_.logDeriv
        (FormalMultilinearSeries.ofScalarsSum (E := ℂ) fun n ↦ coeff n f))
      (FormalMultilinearSeries.ofScalars ℂ fun n ↦ coeff n (logDeriv f)) 0 R := by
  let F := FormalMultilinearSeries.ofScalarsSum (E := ℂ) fun n ↦ coeff n f
  let G := _root_.logDeriv F
  have hR0e : (0 : ENNReal) < R := by exact_mod_cast hR0
  have hfr : 0 < (FormalMultilinearSeries.ofScalars ℂ fun n ↦ coeff n f).radius :=
    hR0e.trans (hRr.trans_le hr)
  have hr0 : 0 < r := hR0e.trans hRr
  have hseries :=
    ((FormalMultilinearSeries.ofScalars ℂ fun n ↦ coeff n f).hasFPowerSeriesOnBall hfr).mono
      hr0 hr
  have hFa : AnalyticOnNhd ℂ F (Metric.eball 0 r) := by
    simpa [F, FormalMultilinearSeries.ofScalarsSum] using hseries.analyticOnNhd
  have hGa : AnalyticOnNhd ℂ G (Metric.eball 0 r) := by
    exact hFa.deriv.div hFa fun w hw ↦ hne w (by
      simpa only [Metric.mem_eball, edist_zero_right] using hw)
  have hG0 : AnalyticAt ℂ G 0 := hGa 0 (Metric.mem_eball_self hr0)
  have hTaylor := hG0.hasFPowerSeriesAt
  have hcoeff : (fun n ↦ coeff n (logDeriv f)) =
      fun n ↦ iteratedDeriv n G 0 / n.factorial := by
    funext n
    simpa [G, F] using coeff_logDeriv_eq_iteratedDeriv f hf0 hfr n
  have hformal : (FormalMultilinearSeries.ofScalars ℂ fun n ↦ coeff n f.logDeriv) =
      FormalMultilinearSeries.ofScalars ℂ
        (fun n ↦ iteratedDeriv n G 0 / n.factorial) := by
    rw [hcoeff]
  rw [← hformal] at hTaylor
  have hclosed : Metric.closedBall (0 : ℂ) R ⊆ Metric.eball 0 r := by
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right] at hw
    rw [Metric.mem_eball, edist_zero_right]
    rw [enorm_eq_nnnorm]
    exact (ENNReal.coe_le_coe.mpr (by exact_mod_cast hw)).trans_lt hRr
  have hRseries := (hGa.differentiableOn.mono hclosed).hasFPowerSeriesOnBall hR0
  obtain ⟨r₀, hr₀⟩ := hTaylor
  exact hr₀.exchange_radius hRseries

/-- **A formal logarithmic derivative sums to the analytic logarithmic derivative throughout a
zero-free disk.** Let `f` be a complex power series with constant coefficient one. If its analytic
sum has no zero in a disk inside its disk of convergence, then the coefficient series of
`f.logDeriv` sums to the analytic logarithmic derivative at every point of the smaller disk. -/
theorem hasSum_coeff_logDeriv_mul_pow_of_zeroFree (f : ℂ⟦X⟧)
    (hf0 : constantCoeff f = 1) {r : ENNReal}
    (hr : r ≤ (FormalMultilinearSeries.ofScalars ℂ fun n ↦ coeff n f).radius)
    (hne : ∀ z : ℂ, ‖z‖ₑ < r →
      FormalMultilinearSeries.ofScalarsSum (E := ℂ) (fun n ↦ coeff n f) z ≠ 0)
    {z : ℂ} (hz : ‖z‖ₑ < r) :
    HasSum (fun n : ℕ ↦ coeff n (logDeriv f) * z ^ n)
      (_root_.logDeriv
        (FormalMultilinearSeries.ofScalarsSum (E := ℂ) fun n ↦ coeff n f) z) := by
  obtain ⟨R, hzR, hRr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hz
  have hRpos : 0 < R := by
    have hRpos' : (0 : ENNReal) < (R : ENNReal) :=
      (bot_le : (0 : ENNReal) ≤ ‖z‖ₑ).trans_lt hzR
    exact_mod_cast hRpos'
  have hlogSeries := hasFPowerSeriesOnBall_logDeriv_of_zeroFree f hf0 hr hne hRpos hRr
  have hzBall : z ∈ Metric.eball (0 : ℂ) (R : ENNReal) := by
    rw [Metric.mem_eball, edist_zero_right, enorm_lt_coe]
    exact enorm_lt_coe.mp hzR
  simpa [mul_comm] using hlogSeries.hasSum hzBall

/-- A formal logarithmic derivative converges absolutely throughout a zero-free disk. -/
theorem summable_norm_coeff_logDeriv_mul_pow_of_zeroFree (f : ℂ⟦X⟧)
    (hf0 : constantCoeff f = 1) {r : ENNReal}
    (hr : r ≤ (FormalMultilinearSeries.ofScalars ℂ fun n ↦ coeff n f).radius)
    (hne : ∀ z : ℂ, ‖z‖ₑ < r →
      FormalMultilinearSeries.ofScalarsSum (E := ℂ) (fun n ↦ coeff n f) z ≠ 0)
    {z : ℂ} (hz : ‖z‖ₑ < r) :
    Summable fun n : ℕ ↦ ‖coeff n (logDeriv f) * z ^ n‖ := by
  obtain ⟨R, hzR, hRr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hz
  have hRpos : 0 < R := by
    have hRpos' : (0 : ENNReal) < (R : ENNReal) :=
      (bot_le : (0 : ENNReal) ≤ ‖z‖ₑ).trans_lt hzR
    exact_mod_cast hRpos'
  have hseries := hasFPowerSeriesOnBall_logDeriv_of_zeroFree f hf0 hr hne hRpos hRr
  have hz' : z ∈ Metric.eball (0 : ℂ)
      (FormalMultilinearSeries.ofScalars ℂ fun n ↦ coeff n (logDeriv f)).radius := by
    rw [Metric.mem_eball, edist_zero_right]
    exact hzR.trans_le hseries.r_le
  exact ((FormalMultilinearSeries.ofScalars ℂ fun n ↦ coeff n (logDeriv f))
    |>.summable_norm_apply hz').congr fun n ↦ by
      simp [mul_comm]

/-- A formal logarithmic derivative converges throughout a zero-free disk. -/
theorem summable_coeff_logDeriv_mul_pow_of_zeroFree (f : ℂ⟦X⟧)
    (hf0 : constantCoeff f = 1) {r : ENNReal}
    (hr : r ≤ (FormalMultilinearSeries.ofScalars ℂ fun n ↦ coeff n f).radius)
    (hne : ∀ z : ℂ, ‖z‖ₑ < r →
      FormalMultilinearSeries.ofScalarsSum (E := ℂ) (fun n ↦ coeff n f) z ≠ 0)
    {z : ℂ} (hz : ‖z‖ₑ < r) :
    Summable fun n : ℕ ↦ coeff n (logDeriv f) * z ^ n :=
  (summable_norm_coeff_logDeriv_mul_pow_of_zeroFree f hf0 hr hne hz).of_norm

/-- One step of the coefficient recurrence, in absolute value: the degree-`m` coefficient of
`f'/f`, weighted by `r ^ (m + 1)`, is bounded by the matching term of `r f'(r)` plus the earlier
weighted coefficients against the weighted coefficients of `f - 1`. -/
private theorem norm_coeff_logDeriv_mul_pow_succ_le (f : ℂ⟦X⟧) (hf0 : constantCoeff f = 1)
    {r : ℝ} (hr : 0 ≤ r) (m : ℕ) :
    ‖coeff m (logDeriv f)‖ * r ^ (m + 1) ≤
      ((m + 1 : ℕ) : ℝ) * ‖coeff (m + 1) f‖ * r ^ (m + 1) +
        ∑ i ∈ Finset.range m, ‖coeff i (logDeriv f)‖ * r ^ (i + 1) *
          (‖coeff (m - i) f‖ * r ^ (m - i)) := by
  have hrec := coeff_logDeriv_recurrence f hf0 m
  rw [Finset.sum_range_succ, Nat.sub_self, coeff_zero_eq_constantCoeff_apply, hf0,
    mul_one] at hrec
  have hcoeff : coeff m (logDeriv f) = (m + 1 : ℂ) * coeff (m + 1) f -
      ∑ i ∈ Finset.range m, coeff i (logDeriv f) * coeff (m - i) f := by
    rw [← hrec]
    ring
  have hnorm : ‖coeff m (logDeriv f)‖ ≤ ((m + 1 : ℕ) : ℝ) * ‖coeff (m + 1) f‖ +
      ∑ i ∈ Finset.range m, ‖coeff i (logDeriv f)‖ * ‖coeff (m - i) f‖ := by
    rw [hcoeff]
    refine (norm_sub_le _ _).trans (add_le_add (le_of_eq ?_) ?_)
    · rw [norm_mul]
      norm_cast
    · exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ (norm_mul _ _).le)
  calc
    ‖coeff m (logDeriv f)‖ * r ^ (m + 1) ≤ (((m + 1 : ℕ) : ℝ) * ‖coeff (m + 1) f‖ +
        ∑ i ∈ Finset.range m, ‖coeff i (logDeriv f)‖ * ‖coeff (m - i) f‖) * r ^ (m + 1) :=
      mul_le_mul_of_nonneg_right hnorm (pow_nonneg hr _)
    _ = _ := by
      rw [add_mul, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      -- Split the power between the shifted index and its complementary index.
      have hindex : m + 1 = (i + 1) + (m - i) := by
        have hi' := Finset.mem_range.mp hi
        omega
      rw [hindex, pow_add]
      ring

/-- The partial sums of the majorant series of the formal logarithmic derivative are bounded by
`T / (1 - t)`, where `T = ∑ n |aₙ| rⁿ` and `t = ∑_{n ≥ 1} |aₙ| rⁿ`. -/
private theorem sum_range_norm_coeff_logDeriv_mul_pow_succ_le (f : ℂ⟦X⟧) (hf0 : constantCoeff f = 1)
    {r : ℝ} (hr : 0 ≤ r) (hsum : Summable fun n : ℕ ↦ n * ‖coeff n f‖ * r ^ n)
    (ht : ∑' n : ℕ, ‖coeff (n + 1) f‖ * r ^ (n + 1) < 1) (N : ℕ) :
    ∑ m ∈ Finset.range N, ‖coeff m (logDeriv f)‖ * r ^ (m + 1) ≤
      (∑' n : ℕ, n * ‖coeff n f‖ * r ^ n) /
        (1 - ∑' n : ℕ, ‖coeff (n + 1) f‖ * r ^ (n + 1)) := by
  set t := ∑' n : ℕ, ‖coeff (n + 1) f‖ * r ^ (n + 1)
  set u : ℕ → ℝ := fun m ↦ ‖coeff m (logDeriv f)‖ * r ^ (m + 1) with hu
  set c : ℕ → ℝ := fun j ↦ ‖coeff j f‖ * r ^ j with hc
  have hsum' : Summable fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) * ‖coeff (n + 1) f‖ * r ^ (n + 1) :=
    (summable_nat_add_iff 1).mpr hsum
  have hc_summable : Summable fun n ↦ c (n + 1) :=
    hsum'.of_nonneg_of_le (fun n ↦ by positivity) fun n ↦ by
      rw [hc, mul_assoc]
      exact le_mul_of_one_le_left (by positivity) (by exact_mod_cast n.succ_pos)
  -- The first part of each recurrence step is dominated by `T`.
  have hA : ∑ m ∈ Finset.range N, ((m + 1 : ℕ) : ℝ) * ‖coeff (m + 1) f‖ * r ^ (m + 1) ≤
      ∑' n : ℕ, n * ‖coeff n f‖ * r ^ n := by
    rw [hsum.tsum_eq_zero_add, Nat.cast_zero, zero_mul, zero_mul, zero_add]
    exact hsum'.sum_le_tsum _ fun n _ ↦ by positivity
  -- The convolution part is at most `t` times the partial sum itself.
  have hB : ∑ m ∈ Finset.range N, ∑ i ∈ Finset.range m, u i * c (m - i) ≤
      t * ∑ i ∈ Finset.range N, u i := by
    simp only [Finset.range_eq_Ico]
    rw [← Finset.sum_Ico_Ico_comm', Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    rw [← Finset.mul_sum, mul_comm t]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (norm_nonneg _) (pow_nonneg hr _))
    rw [Finset.sum_Ico_eq_sum_range]
    calc
      ∑ k ∈ Finset.range (N - (i + 1)), c (i + 1 + k - i) =
          ∑ k ∈ Finset.range (N - (i + 1)), c (k + 1) :=
        Finset.sum_congr rfl fun k _ ↦ by
          -- Reindex after removing the outer index `i`.
          have hindex : i + 1 + k - i = k + 1 := by omega
          rw [hindex]
      _ ≤ t := hc_summable.sum_le_tsum _ fun n _ ↦ by positivity
  have hU : ∑ m ∈ Finset.range N, u m ≤
      ∑' n : ℕ, n * ‖coeff n f‖ * r ^ n + t * ∑ m ∈ Finset.range N, u m := by
    calc
      ∑ m ∈ Finset.range N, u m ≤ ∑ m ∈ Finset.range N,
          (((m + 1 : ℕ) : ℝ) * ‖coeff (m + 1) f‖ * r ^ (m + 1) +
            ∑ i ∈ Finset.range m, u i * c (m - i)) :=
        Finset.sum_le_sum fun m _ ↦ norm_coeff_logDeriv_mul_pow_succ_le f hf0 hr m
      _ ≤ _ := by
        rw [Finset.sum_add_distrib]
        exact add_le_add hA hB
  rw [le_div_iff₀ (sub_pos.mpr ht)]
  linarith

/-- Under the hypotheses of `PowerSeries.tsum_norm_coeff_logDeriv_mul_pow_succ_le`, the series
`∑ m, |[Xᵐ] (f'/f)| r ^ (m + 1)` converges. -/
theorem summable_norm_coeff_logDeriv_mul_pow_succ (f : ℂ⟦X⟧) (hf0 : constantCoeff f = 1)
    {r : ℝ} (hr : 0 ≤ r) (hsum : Summable fun n : ℕ ↦ n * ‖coeff n f‖ * r ^ n)
    (ht : ∑' n : ℕ, ‖coeff (n + 1) f‖ * r ^ (n + 1) < 1) :
    Summable fun m : ℕ ↦ ‖coeff m (logDeriv f)‖ * r ^ (m + 1) :=
  summable_of_sum_range_le (fun _ ↦ by positivity)
    (sum_range_norm_coeff_logDeriv_mul_pow_succ_le f hf0 hr hsum ht)

/-- **A majorant for the coefficients of a formal logarithmic derivative.** Write `aₙ` for the
coefficients of `f`, where `a₀ = 1`, and let `r ≥ 0`. If `T = ∑ n |aₙ| rⁿ` converges and
`t = ∑_{n ≥ 1} |aₙ| rⁿ < 1`, then `∑ m, |[Xᵐ] (f'/f)| r ^ (m + 1) ≤ T / (1 - t)`.

For the majorant `F(X) = ∑ |aₙ| Xⁿ` this reads `∑ m, |[Xᵐ] (X f'/f)| rᵐ ≤ r F'(r) / (2 - F(r))`.
No zero-freeness hypothesis is needed beyond `t < 1`, and the bound is uniform in `f`, which is
what makes it summable over a family of power series. -/
theorem tsum_norm_coeff_logDeriv_mul_pow_succ_le (f : ℂ⟦X⟧) (hf0 : constantCoeff f = 1)
    {r : ℝ} (hr : 0 ≤ r) (hsum : Summable fun n : ℕ ↦ n * ‖coeff n f‖ * r ^ n)
    (ht : ∑' n : ℕ, ‖coeff (n + 1) f‖ * r ^ (n + 1) < 1) :
    ∑' m : ℕ, ‖coeff m (logDeriv f)‖ * r ^ (m + 1) ≤
      (∑' n : ℕ, n * ‖coeff n f‖ * r ^ n) /
        (1 - ∑' n : ℕ, ‖coeff (n + 1) f‖ * r ^ (n + 1)) :=
  Real.tsum_le_of_sum_range_le (fun _ ↦ by positivity)
    (sum_range_norm_coeff_logDeriv_mul_pow_succ_le f hf0 hr hsum ht)

end PowerSeries
