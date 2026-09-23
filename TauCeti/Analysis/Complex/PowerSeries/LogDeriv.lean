/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.OfScalars
public import TauCeti.RingTheory.PowerSeries.Log
public import Mathlib.Analysis.Complex.TaylorSeries

import TauCeti.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Convergence of formal logarithms and logarithmic derivatives

This file connects the formal logarithm and logarithmic derivative of a complex power series to
its analytic sum. If a power series has constant coefficient one and its analytic sum has no zero
in its disk of convergence, then its formal logarithm and logarithmic derivative converge
throughout that disk. Exponentiating the sum of the formal logarithm recovers the original series.

The zero-free hypothesis is essential: the radius of the logarithmic derivative is limited by the
nearest zero of the original series, even when the original series converges farther.

## Main results

* `PowerSeries.hasSum_coeff_logDeriv_mul_pow_of_zeroFree`: evaluation of the formal
  logarithmic derivative throughout a zero-free convergence disk.
* `PowerSeries.summable_norm_coeff_logDeriv_mul_pow_of_zeroFree`: absolute convergence of the
  formal logarithmic derivative throughout a zero-free convergence disk.
* `PowerSeries.summable_norm_coeff_logOf_mul_pow_of_zeroFree`: absolute convergence of the formal
  logarithm throughout a zero-free convergence disk.
* `PowerSeries.exp_tsum_coeff_logOf_mul_pow_of_zeroFree`: exponentiating the sum of the formal
  logarithm recovers the original series.
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

/-- The formal logarithm converges absolutely throughout every zero-free disk on which the
original power series converges. -/
theorem summable_norm_coeff_logOf_mul_pow_of_zeroFree (f : ℂ⟦X⟧)
    (hf0 : constantCoeff f = 1) {r : ENNReal}
    (hr : r ≤ (FormalMultilinearSeries.ofScalars ℂ fun n ↦ coeff n f).radius)
    (hne : ∀ z : ℂ, ‖z‖ₑ < r →
      FormalMultilinearSeries.ofScalarsSum (E := ℂ) (fun n ↦ coeff n f) z ≠ 0)
    {z : ℂ} (hz : ‖z‖ₑ < r) :
    Summable fun n : ℕ ↦ ‖coeff n (logOf f) * z ^ n‖ := by
  rw [← summable_nat_add_iff 1]
  refine (summable_norm_coeff_logDeriv_mul_pow_of_zeroFree f hf0 hr hne hz).mul_left ‖z‖
    |>.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun n ↦ ?_
  have hn : (1 : ℝ) ≤ ‖(n : ℂ) + 1‖ := by
    rw [show (n : ℂ) + 1 = (n + 1 : ℕ) by norm_num, Complex.norm_natCast]
    norm_num
  rw [coeff_logDeriv, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, pow_succ]
  calc
    ‖coeff (n + 1) (logOf f)‖ * (‖z‖ ^ n * ‖z‖) =
        ‖coeff (n + 1) (logOf f)‖ * ‖z‖ ^ n * ‖z‖ * 1 := by ring
    _ ≤ ‖coeff (n + 1) (logOf f)‖ * ‖z‖ ^ n * ‖z‖ * ‖(n : ℂ) + 1‖ :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    _ = ‖z‖ * (‖coeff (n + 1) (logOf f)‖ * ‖(n : ℂ) + 1‖ * ‖z‖ ^ n) := by ring

/-- **The evaluated formal logarithm exponentiates to the original power series.** If a complex
power series has constant coefficient one and is zero-free in a disk of convergence, then its
formal logarithm converges throughout that disk and its exponential is the analytic sum of the
original series. -/
theorem exp_tsum_coeff_logOf_mul_pow_of_zeroFree (f : ℂ⟦X⟧)
    (hf0 : constantCoeff f = 1) {r : ENNReal}
    (hr : r ≤ (FormalMultilinearSeries.ofScalars ℂ fun n ↦ coeff n f).radius)
    (hne : ∀ z : ℂ, ‖z‖ₑ < r →
      FormalMultilinearSeries.ofScalarsSum (E := ℂ) (fun n ↦ coeff n f) z ≠ 0)
    {z : ℂ} (hz : ‖z‖ₑ < r) :
    Complex.exp (∑' n : ℕ, coeff n (logOf f) * z ^ n) =
      FormalMultilinearSeries.ofScalarsSum (E := ℂ) (fun n ↦ coeff n f) z := by
  let F := FormalMultilinearSeries.ofScalarsSum (E := ℂ) fun n ↦ coeff n f
  let G := _root_.logDeriv F
  obtain ⟨R₂, hzR₂, hR₂r⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hz
  obtain ⟨R₁, hzR₁, hR₁R₂⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hzR₂
  have hR₂pos : 0 < R₂ := by
    have : (0 : ENNReal) < (R₂ : ENNReal) :=
      (bot_le : (0 : ENNReal) ≤ ‖z‖ₑ).trans_lt hzR₂
    exact_mod_cast this
  have hfr : 0 < (FormalMultilinearSeries.ofScalars ℂ fun n ↦ coeff n f).radius :=
    (show (0 : ENNReal) < R₂ by exact_mod_cast hR₂pos).trans (hR₂r.trans_le hr)
  have hFseries :=
    ((FormalMultilinearSeries.ofScalars ℂ fun n ↦ coeff n f).hasFPowerSeriesOnBall hfr).mono
      (show (0 : ENNReal) < R₂ by exact_mod_cast hR₂pos) (hR₂r.le.trans hr)
  have hFd : DifferentiableOn ℂ F (Metric.ball 0 R₂) := by
    intro w hw
    have hw' : w ∈ Metric.eball (0 : ℂ) (R₂ : ENNReal) := by
      rw [Metric.mem_eball, edist_zero_right, enorm_lt_coe]
      exact NNReal.coe_lt_coe.mp (by simpa using Metric.mem_ball.mp hw)
    exact (hFseries.analyticAt_of_mem hw').differentiableAt.differentiableWithinAt
  have hFzero : (0 : ℂ) ∉ F '' Metric.ball 0 R₂ := by
    rintro ⟨w, hw, hw0⟩
    apply hne w
    · exact (show ‖w‖ₑ < (R₂ : ENNReal) by
        rw [enorm_lt_coe]
        exact NNReal.coe_lt_coe.mp (by simpa using Metric.mem_ball.mp hw)).trans hR₂r
    · exact hw0
  have hsc : IsSimplyConnected (Metric.ball (0 : ℂ) R₂) := by
    have : ContractibleSpace (Metric.ball (0 : ℂ) R₂) :=
      Metric.contractibleSpace_ball hR₂pos
    exact SimplyConnectedSpace.ofContractible _
  obtain ⟨L, hLd, hLexp⟩ := TauCeti.exists_differentiableOn_eqOn_exp_comp
    hsc Metric.isOpen_ball hFd hFzero
  let L₀ : ℂ → ℂ := fun w ↦ L w - L 0
  have hzeroBall : (0 : ℂ) ∈ Metric.ball 0 R₂ := Metric.mem_ball_self hR₂pos
  have hF0 : F 0 = 1 := by
    simpa [F, FormalMultilinearSeries.ofScalarsSum_zero, constantCoeff] using hf0
  have hLexp0 : Complex.exp (L 0) = 1 := by
    rw [← hF0]
    exact hLexp hzeroBall
  have hL₀d : DifferentiableOn ℂ L₀ (Metric.ball 0 R₂) :=
    hLd.sub (differentiableOn_const (c := L 0))
  have hL₀exp : Set.EqOn (Complex.exp ∘ L₀) F (Metric.ball 0 R₂) := by
    intro w hw
    simp only [Function.comp_apply, L₀, Complex.exp_sub, hLexp0, div_one]
    exact hLexp hw
  have hderiv : deriv L₀ =ᶠ[𝓝 0] G := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hzeroBall] with w hw
    have hLdw : DifferentiableAt ℂ L w := (hLd w hw).differentiableAt
      (Metric.isOpen_ball.mem_nhds hw)
    have hsub : deriv L₀ w = deriv L w := (hLdw.hasDerivAt.sub_const (L 0)).deriv
    rw [hsub]
    exact TauCeti.deriv_eq_logDeriv_of_eqOn_exp_comp Metric.isOpen_ball hLd hLexp hw
  have hL₀a : AnalyticAt ℂ L₀ 0 := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [Metric.isOpen_ball.mem_nhds hzeroBall] with w hw
    exact (hL₀d w hw).differentiableAt (Metric.isOpen_ball.mem_nhds hw)
  have hcoeff : (fun n ↦ coeff n (logOf f)) =
      fun n ↦ iteratedDeriv n L₀ 0 / n.factorial := by
    funext n
    cases n with
    | zero => simp [L₀, constantCoeff_logOf hf0]
    | succ n =>
        have hb := coeff_logDeriv_eq_iteratedDeriv f hf0 hfr n
        rw [coeff_logDeriv] at hb
        rw [iteratedDeriv_succ', hderiv.iteratedDeriv_eq]
        push_cast [Nat.factorial_succ] at hb ⊢
        field_simp at hb ⊢
        exact hb
  have hformal : (FormalMultilinearSeries.ofScalars ℂ fun n ↦ coeff n (logOf f)) =
      FormalMultilinearSeries.ofScalars ℂ
        (fun n ↦ iteratedDeriv n L₀ 0 / n.factorial) := by
    rw [hcoeff]
  have hTaylor := hL₀a.hasFPowerSeriesAt
  rw [← hformal] at hTaylor
  have hR₁pos : 0 < R₁ := by
    have : (0 : ENNReal) < (R₁ : ENNReal) :=
      (bot_le : (0 : ENNReal) ≤ ‖z‖ₑ).trans_lt hzR₁
    exact_mod_cast this
  have hclosed : Metric.closedBall (0 : ℂ) R₁ ⊆ Metric.ball 0 R₂ := by
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right] at hw
    rw [Metric.mem_ball, dist_zero_right]
    exact hw.trans_lt (by exact_mod_cast hR₁R₂)
  have hR₁series := (hL₀d.mono hclosed).hasFPowerSeriesOnBall hR₁pos
  obtain ⟨r₀, hr₀⟩ := hTaylor
  have hlogSeries := hr₀.exchange_radius hR₁series
  have hzBall : z ∈ Metric.eball (0 : ℂ) (R₁ : ENNReal) := by
    rw [Metric.mem_eball, edist_zero_right]
    exact hzR₁
  have hsum : HasSum (fun n : ℕ ↦ coeff n (logOf f) * z ^ n) (L₀ z) := by
    simpa [mul_comm] using hlogSeries.hasSum hzBall
  rw [hsum.tsum_eq]
  exact hL₀exp (by
    rw [Metric.mem_ball, dist_zero_right]
    exact_mod_cast hzR₂)

end PowerSeries
