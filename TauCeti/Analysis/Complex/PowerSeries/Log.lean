/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.PowerSeries.LogDeriv
import TauCeti.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Formal logarithms of zero-free complex power series

A zero-free analytic power series has a convergent formal logarithm on the same disk.
The normalized analytic logarithm has the formal logarithm as its Taylor series, so
exponentiating the evaluated formal logarithm recovers the original analytic sum.

## Main results

* `PowerSeries.summable_norm_coeff_logOf_mul_pow_of_zeroFree`: absolute convergence of the
  formal logarithm throughout a zero-free convergence disk.
* `PowerSeries.exp_tsum_coeff_logOf_mul_pow_of_zeroFree`: exponentiation recovers the original
  power series.
-/

public section

namespace PowerSeries

open Filter
open scoped Topology

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
  have hcast : (n : ℂ) + 1 = ((n + 1 : ℕ) : ℂ) := by norm_num
  have hn : (1 : ℝ) ≤ ‖(n : ℂ) + 1‖ := by
    rw [hcast, Complex.norm_natCast]
    norm_num
  rw [coeff_logDeriv, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, pow_succ]
  calc
    ‖coeff (n + 1) (logOf f)‖ * (‖z‖ ^ n * ‖z‖) =
        ‖coeff (n + 1) (logOf f)‖ * ‖z‖ ^ n * ‖z‖ * 1 := by ring
    _ ≤ ‖coeff (n + 1) (logOf f)‖ * ‖z‖ ^ n * ‖z‖ * ‖(n : ℂ) + 1‖ :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    _ = ‖z‖ * (‖coeff (n + 1) (logOf f)‖ * ‖(n : ℂ) + 1‖ * ‖z‖ ^ n) := by ring

private theorem coeff_logOf_eq_iteratedDeriv_of_deriv_eq (f : ℂ⟦X⟧)
    (hf0 : constantCoeff f = 1)
    (hfr : 0 < (FormalMultilinearSeries.ofScalars ℂ fun n ↦ coeff n f).radius)
    (L₀ : ℂ → ℂ) (hL₀zero : L₀ 0 = 0)
    (hderiv : deriv L₀ =ᶠ[𝓝 0]
      _root_.logDeriv (FormalMultilinearSeries.ofScalarsSum (E := ℂ) fun n ↦ coeff n f))
    (n : ℕ) :
    coeff n (logOf f) = iteratedDeriv n L₀ 0 / n.factorial := by
  cases n with
  | zero => simp [constantCoeff_logOf hf0, hL₀zero]
  | succ n =>
      have hb := coeff_logDeriv_eq_iteratedDeriv f hf0 hfr n
      rw [coeff_logDeriv] at hb
      rw [iteratedDeriv_succ', hderiv.iteratedDeriv_eq]
      push_cast [Nat.factorial_succ] at hb ⊢
      field_simp at hb ⊢
      exact hb

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
  -- Choose nested disks: the outer disk supports a logarithm, and the inner one supports
  -- its Taylor expansion at zero and contains the evaluation point.
  obtain ⟨R₂, hzR₂, hR₂r⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hz
  obtain ⟨R₁, hzR₁, hR₁R₂⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hzR₂
  have hR₂pos : 0 < R₂ := by
    have : (0 : ENNReal) < (R₂ : ENNReal) :=
      (bot_le : (0 : ENNReal) ≤ ‖z‖ₑ).trans_lt hzR₂
    exact_mod_cast this
  have hR₂posE : (0 : ENNReal) < (R₂ : ENNReal) := by exact_mod_cast hR₂pos
  have hfr : 0 < (FormalMultilinearSeries.ofScalars ℂ fun n ↦ coeff n f).radius :=
    hR₂posE.trans (hR₂r.trans_le hr)
  have hFseries :=
    ((FormalMultilinearSeries.ofScalars ℂ fun n ↦ coeff n f).hasFPowerSeriesOnBall hfr).mono
      hR₂posE (hR₂r.le.trans hr)
  have hFd : DifferentiableOn ℂ F (Metric.ball 0 R₂) := by
    intro w hw
    have hw' : w ∈ Metric.eball (0 : ℂ) (R₂ : ENNReal) := by
      rw [Metric.mem_eball, edist_zero_right, enorm_lt_coe]
      exact NNReal.coe_lt_coe.mp (by simpa using Metric.mem_ball.mp hw)
    exact (hFseries.analyticAt_of_mem hw').differentiableAt.differentiableWithinAt
  have hFzero : (0 : ℂ) ∉ F '' Metric.ball 0 R₂ := by
    rintro ⟨w, hw, hw0⟩
    apply hne w
    · have hwR₂ : ‖w‖ₑ < (R₂ : ENNReal) := by
        rw [enorm_lt_coe]
        exact NNReal.coe_lt_coe.mp (by simpa using Metric.mem_ball.mp hw)
      exact hwR₂.trans hR₂r
    · exact hw0
  have hsc : IsSimplyConnected (Metric.ball (0 : ℂ) R₂) := by
    have : ContractibleSpace (Metric.ball (0 : ℂ) R₂) :=
      Metric.contractibleSpace_ball hR₂pos
    exact SimplyConnectedSpace.ofContractible _
  obtain ⟨L, hLd, hLexp⟩ := TauCeti.exists_differentiableOn_eqOn_exp_comp
    hsc Metric.isOpen_ball hFd hFzero
  -- Normalize the analytic logarithm at zero; this removes the integral multiple of 2πi.
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
  -- The coefficient lemma identifies this normalized logarithm with the formal log.
  have hcoeff : (fun n ↦ coeff n (logOf f)) =
      fun n ↦ iteratedDeriv n L₀ 0 / n.factorial := by
    funext n
    exact coeff_logOf_eq_iteratedDeriv_of_deriv_eq f hf0 hfr L₀ (by simp [L₀]) hderiv n
  have hformal : (FormalMultilinearSeries.ofScalars ℂ fun n ↦ coeff n (logOf f)) =
      FormalMultilinearSeries.ofScalars ℂ
        (fun n ↦ iteratedDeriv n L₀ 0 / n.factorial) := by
    rw [hcoeff]
  -- Exchange the Taylor radius with the inner disk, then evaluate the series at z.
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
