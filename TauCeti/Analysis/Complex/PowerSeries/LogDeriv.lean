/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Log
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Convergence of formal logarithmic derivatives

This file connects the formal logarithmic derivative of a complex power series to the analytic
logarithmic derivative of its sum. If a power series has constant coefficient one and its analytic
sum has no zero in its disk of convergence, then its formal logarithmic derivative converges
throughout that disk.

The zero-free hypothesis is essential: the radius of the logarithmic derivative is limited by the
nearest zero of the original series, even when the original series converges farther.

## Main result

* `PowerSeries.summable_coeff_logDeriv_mul_pow_of_zeroFree`: convergence of the formal
  logarithmic derivative throughout a zero-free convergence disk.
-/

public section

namespace PowerSeries

open Filter
open scoped Topology

private theorem iteratedDeriv_analyticSum_zero (f : ℂ⟦X⟧)
    (hf : 0 < (FormalMultilinearSeries.ofScalars ℂ fun n ↦ coeff n f).radius) (n : ℕ) :
    iteratedDeriv n (FormalMultilinearSeries.ofScalarsSum (E := ℂ) fun n ↦ coeff n f) 0 =
      n.factorial * coeff n f := by
  have hseries :=
    (FormalMultilinearSeries.ofScalars ℂ fun n ↦ coeff n f).hasFPowerSeriesOnBall hf
  have hfac := hseries.factorial_smul (1 : ℂ)
  simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, one_pow, one_mul, smul_eq_mul,
    FormalMultilinearSeries.coeff_ofScalars] at hfac
  have h := hfac n
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod] at h
  simpa [FormalMultilinearSeries.ofScalarsSum, mul_comm] using h.symm

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
    simpa [F] using iteratedDeriv_analyticSum_zero f hf k
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

private theorem coeff_logDeriv_eq_iteratedDeriv (f : ℂ⟦X⟧)
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

/-- **A formal logarithmic derivative converges throughout a zero-free disk.** Let `f` be a
complex power series with constant coefficient one. If its analytic sum has no zero in a disk
inside its disk of convergence, then the coefficient series of `f.logDeriv` is summable at every
point of the smaller disk. -/
theorem summable_coeff_logDeriv_mul_pow_of_zeroFree (f : ℂ⟦X⟧)
    (hf0 : constantCoeff f = 1) {r : ENNReal} (hr0 : 0 < r)
    (hr : r ≤ (FormalMultilinearSeries.ofScalars ℂ fun n ↦ coeff n f).radius)
    (hne : ∀ z : ℂ, ‖z‖ₑ < r →
      FormalMultilinearSeries.ofScalarsSum (E := ℂ) (fun n ↦ coeff n f) z ≠ 0)
    {z : ℂ} (hz : ‖z‖ₑ < r) :
    Summable fun n : ℕ ↦ coeff n (logDeriv f) * z ^ n := by
  let F := FormalMultilinearSeries.ofScalarsSum (E := ℂ) fun n ↦ coeff n f
  let G := _root_.logDeriv F
  have hfr : 0 < (FormalMultilinearSeries.ofScalars ℂ fun n ↦ coeff n f).radius :=
    hr0.trans_le hr
  have hseries :=
    ((FormalMultilinearSeries.ofScalars ℂ fun n ↦ coeff n f).hasFPowerSeriesOnBall hfr).mono
      hr0 hr
  have hFa : AnalyticOnNhd ℂ F (Metric.eball 0 r) := by
    simpa [F, FormalMultilinearSeries.ofScalarsSum] using hseries.analyticOnNhd
  have hGa : AnalyticOnNhd ℂ G (Metric.eball 0 r) := by
    exact hFa.deriv.div hFa fun w hw ↦ hne w (by simpa only [Metric.mem_eball, edist_zero_right]
      using hw)
  have hG0 : AnalyticAt ℂ G 0 := hGa 0 (Metric.mem_eball_self hr0)
  have hTaylor := hG0.hasFPowerSeriesAt
  have hcoeff : (fun n ↦ coeff n (logDeriv f)) =
      fun n ↦ iteratedDeriv n G 0 / n.factorial := by
    funext n
    simpa [G] using coeff_logDeriv_eq_iteratedDeriv f hf0 hfr n
  have hformal : (FormalMultilinearSeries.ofScalars ℂ fun n ↦ coeff n f.logDeriv) =
      FormalMultilinearSeries.ofScalars ℂ
        (fun n ↦ iteratedDeriv n G 0 / n.factorial) := by
    rw [hcoeff]
  rw [← hformal] at hTaylor
  obtain ⟨R, hzR, hRr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hz
  have hRpos : 0 < R := by
    have hRpos' : (0 : ENNReal) < (R : ENNReal) :=
      (bot_le : (0 : ENNReal) ≤ ‖z‖ₑ).trans_lt hzR
    exact_mod_cast hRpos'
  have hclosed : Metric.closedBall (0 : ℂ) R ⊆
      Metric.eball 0 r := by
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right] at hw
    rw [Metric.mem_eball, edist_zero_right]
    rw [enorm_eq_nnnorm]
    exact (ENNReal.coe_le_coe.mpr (by exact_mod_cast hw)).trans_lt hRr
  have hRseries := (hGa.differentiableOn.mono hclosed).hasFPowerSeriesOnBall hRpos
  obtain ⟨r, hr⟩ := hTaylor
  have hlogSeries := hr.exchange_radius hRseries
  have hzBall : z ∈ Metric.eball (0 : ℂ) (R : ENNReal) := by
    rw [Metric.mem_eball, edist_zero_right, enorm_lt_coe]
    exact enorm_lt_coe.mp hzR
  refine (hlogSeries.hasSum hzBall).summable.congr fun n ↦ ?_
  simp [mul_comm]

end PowerSeries
