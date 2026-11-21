/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.LSeries.Basic
public import TauCeti.NumberTheory.LSeries.BoundaryConvergence.StepCorrection
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.Analysis.Complex.PowerSeries.Fejer
import TauCeti.Analysis.SpecialFunctions.Log.Base
import TauCeti.NumberTheory.LSeries.BoundaryConvergence.Endpoint

/-!
# Continuous boundary values do not force boundary convergence

Newman's Tauberian theorem (`newmanLaplace_tendsto_integral`) and the bounded Dirichlet endpoint
theorem (`boundedDirichlet_tendsto_ordered_at_one`) both require a holomorphic continuation across
an open neighbourhood of the closed right half-plane. This file proves that continuity up to the
boundary line—even together with holomorphy on the open half-plane and vanishing of the integrand
or coefficients at infinity—does not suffice in either setting.

The construction transfers Fejér's 1911 disc-algebra power series
(`TauCeti.exists_continuousOn_closedBall_hasSum_unbounded_sum_range`) to Laplace transforms and
Dirichlet series:

* **Bounded Laplace transforms.** For a bounded sequence `c : ℕ → ℝ` with disc-algebra generating
  function `P`, the unit step function `f t = c ⌊t⌋₊` satisfies `|f t| ≤ 1`, `f t → 0`, and its
  Laplace transform on `0 < re z` is `(∫ u in 0..1, exp (-z * u)) * P (exp (-z))`
  (`TauCeti.integral_floor_div_mul_cexp_neg_mul`), which extends continuously to `0 ≤ re z` and
  holomorphically to `0 < re z`. Yet at `T = N`, `∫ t in 0..N, f t = ∑ n ∈ range N, c n` is
  unbounded above, so `∫ t in 0..T, f t` fails to converge and no holomorphic continuation exists
  on any open set containing `{z | 0 ≤ z.re}`
  (`exists_bounded_continuousOn_laplace_not_tendsto_intervalIntegral`).
* **Bounded Dirichlet series.** For any integer base `b > 1`, the identity
  `Nat.log b ⌊exp t⌋₊ = ⌊t / log b⌋₊` (`Real.natFloor_logb_eq_natLog_natFloor`) identifies the
  exponential step function of the block-constant sequence `a n = c (Nat.log b n)` (`n ≥ 1`,
  `a 0 = 0`) pointwise with the uniform step function `t ↦ c ⌊t / log b⌋₊`. Combining
  `integral_floor_exp_mul_cexp_neg_mul` with `TauCeti.integral_floor_div_mul_cexp_neg_mul`
  expresses `LSeries a (z + 1) + stepCorrection a z` in terms of `P (exp (-log b * z))`
  (`LSeries_natLog_add_stepCorrection`), while at cutoffs `N = b ^ K - 1` the ordered harmonic sum
  plus the step correction equals `log b * ∑ k ∈ range K, c k`
  (`sum_Icc_natLog_div_add_stepCorrectionTerm`). Because the step correction is holomorphic on
  `-1 < re z` and converges absolutely at `z = 0`, taking `b = 2` with Fejér's `(c, P)` yields
  real coefficients `a` with `|a n| ≤ 1`, `a n → 0`, and vanishing Cesàro mean
  `x⁻¹ * ∑ n ∈ Icc 1 ⌊x⌋₊, a n → 0`, whose Dirichlet series extends continuously to `1 ≤ re s` and
  holomorphically to `1 < re s` (admitting no holomorphic continuation to any open neighbourhood of
  `{s | 1 ≤ s.re}`), while the ordered harmonic sums `∑ n ∈ Icc 1 N, a n / n` are unbounded above
  (`exists_bounded_continuousOn_LSeries_not_tendsto_sum_Icc_div`).

## Main declarations

* `TauCeti.LSeries.LSeries_natLog_add_stepCorrection`: identity relating the `b`-adic block
  Dirichlet series plus step correction to the power series of the block values at `exp (-log b z)`.
* `TauCeti.LSeries.sum_Icc_natLog_div_add_stepCorrectionTerm`: identity at cutoffs `b ^ K - 1`
  between ordered harmonic sums plus step correction and `log b` times partial sums of the block
  values.
* `TauCeti.LSeries.exists_bounded_continuousOn_laplace_not_tendsto_intervalIntegral`: continuous
  boundary sharpness of Newman's bounded-Laplace Tauberian theorem.
* `TauCeti.LSeries.exists_bounded_continuousOn_LSeries_not_tendsto_sum_Icc_div`: continuous
  boundary sharpness of bounded Dirichlet series boundary convergence, with vanishing Cesàro
  means.

## References

* L. Fejér, *Sur les singularités de la série de Fourier des fonctions continues*, Ann. Sci.
  École Norm. Sup. (3) 28 (1911), 63–104.
* J. Korevaar, *Tauberian Theory: A Century of Developments*, Springer, 2004, Ch. III.
* D. J. Newman, *Simple analytic proof of the prime number theorem*, Amer. Math. Monthly 87
  (1980), 693–696.
-/

public section

open Filter MeasureTheory Set Metric Complex
open scoped Topology Interval

namespace TauCeti.LSeries

/-- **Laplace–Dirichlet bridge for `b`-adic block coefficients.** For an integer base `b > 1`,
a bounded sequence `c : ℕ → ℂ`, and `0 < re z`, the shifted Dirichlet series of
`n ↦ if n = 0 then 0 else c (Nat.log b n)` plus its step correction equals
`(∫ u in 0..log b, exp (-z * u)) * ∑' k, c k * exp (-log b * z) ^ k`. -/
theorem LSeries_natLog_add_stepCorrection {b : ℕ} (hb : 1 < b) {c : ℕ → ℂ} {M : ℝ}
    (hbound : ∀ n, ‖c n‖ ≤ M) {z : ℂ} (hz : 0 < z.re) :
    LSeries (fun n ↦ if n = 0 then 0 else c (Nat.log b n)) (z + 1) +
        stepCorrection (fun n ↦ if n = 0 then 0 else c (Nat.log b n)) z =
      (∫ u in (0 : ℝ)..Real.log b, cexp (-z * u)) *
        ∑' k, c k * cexp (-(Real.log b : ℂ) * z) ^ k := by
  have habound : ∀ n, 1 ≤ n → ‖(if n = 0 then 0 else c (Nat.log b n))‖ ≤ M := by
    intro n hn
    simp [Nat.one_le_iff_ne_zero.mp hn, hbound]
  have hlogb : 0 < Real.log b := Real.log_pos (by exact_mod_cast hb)
  rw [← integral_floor_exp_mul_cexp_neg_mul habound hz,
    ← integral_floor_div_mul_cexp_neg_mul hbound hlogb hz]
  refine setIntegral_congr_fun measurableSet_Ici fun t ht ↦ ?_
  rw [ite_eq_right (Nat.floor_pos.mpr (Real.one_le_exp ht)).ne',
    ← Real.natFloor_logb_eq_natLog_natFloor b (Real.exp_nonneg t), Real.logb, Real.log_exp]

/-- **Partial-sum identity for `b`-adic block coefficients at powers of `b`.** For an integer
base `b > 1`, any sequence `c : ℕ → ℂ`, and every `K : ℕ`, the ordered harmonic partial sum up to
`b ^ K - 1` plus the corresponding partial sum of the step correction at `z = 0` equals
`log b * ∑ k ∈ range K, c k`. -/
theorem sum_Icc_natLog_div_add_stepCorrectionTerm {b : ℕ} (hb : 1 < b) (c : ℕ → ℂ) (K : ℕ) :
    (∑ n ∈ Finset.Icc 1 (b ^ K - 1), c (Nat.log b n) / (n : ℂ)) +
        ∑ n ∈ Finset.range (b ^ K),
          stepCorrectionTerm (fun n ↦ if n = 0 then 0 else c (Nat.log b n)) n 0 =
      (Real.log b : ℂ) * ∑ k ∈ Finset.range K, c k := by
  set a : ℕ → ℂ := fun n ↦ if n = 0 then 0 else c (Nat.log b n)
  have hlogb : 0 < Real.log b := Real.log_pos (by exact_mod_cast hb)
  have hpow_pos : 1 ≤ b ^ K := Nat.one_le_pow K b (by omega)
  have hlog_eq : Real.log (((b ^ K - 1 : ℕ) : ℝ) + 1) = (K : ℝ) * Real.log b := by
    have hcast : (((b ^ K - 1 : ℕ) : ℝ) + 1) = (b : ℝ) ^ K := by
      exact_mod_cast Nat.sub_add_cancel hpow_pos
    rw [hcast, Real.log_pow]
  -- Evaluate the integral of `t ↦ a ⌊exp t⌋₊` over `[0, K * log b]` in two ways.
  have hL := intervalIntegral_floor_exp_mul_cexp_neg_mul_log_succ a (b ^ K - 1) 0
  simp only [neg_zero, zero_mul, Complex.exp_zero, mul_one, zero_add] at hL
  rw [hlog_eq, Nat.sub_add_cancel hpow_pos, Finset.sum_add_distrib] at hL
  have hR := intervalIntegral_floor_div_mul_cexp_neg_mul c hlogb K 0
  simp only [neg_zero, zero_mul, Complex.exp_zero, mul_one,
    intervalIntegral.integral_const, sub_zero] at hR
  have hint_eq : ∫ t in (0 : ℝ)..((K : ℝ) * Real.log b), a ⌊Real.exp t⌋₊ =
      ∫ t in (0 : ℝ)..((K : ℝ) * Real.log b), c ⌊t / Real.log b⌋₊ := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [uIcc_of_le (by positivity)] at ht
    simp only [a, ite_eq_right (Nat.floor_pos.mpr (Real.one_le_exp ht.1)).ne',
      ← Real.natFloor_logb_eq_natLog_natFloor b (Real.exp_nonneg t), Real.logb, Real.log_exp]
  have hterm : ∑ n ∈ Finset.range (b ^ K), LSeries.term a 1 n =
      ∑ n ∈ Finset.Icc 1 (b ^ K - 1), c (Nat.log b n) / (n : ℂ) := by
    rw [← Nat.sub_add_cancel hpow_pos, Finset.range_eq_Ico,
      Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos _), LSeries.term_zero, zero_add, zero_add,
      Nat.succ_eq_add_one, Finset.Ico_add_one_right_eq_Icc]
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hn).1
    rw [LSeries.term_of_ne_zero hn0, Complex.cpow_one]
    simp [a, hn0]
  rw [← hterm, ← hL, hint_eq, hR]
  simp [Complex.real_smul]

/-- **Continuous boundary values do not suffice for Newman's Tauberian theorem.** There exist a
measurable real function `f : ℝ → ℝ` with `|f t| ≤ 1` and `f t → 0` as `t → ∞`, and a function
`G : ℂ → ℂ` continuous on the closed right half-plane `0 ≤ re z` and holomorphic on `0 < re z`
where it agrees with the Laplace transform of `f`, such that:

* the truncated integrals `∫ t in 0..T, f t` are unbounded above and therefore converge to no
  limit `L : ℂ` as `T → ∞`;
* `G` admits no holomorphic continuation to any open neighbourhood of `{z | 0 ≤ z.re}`. -/
theorem exists_bounded_continuousOn_laplace_not_tendsto_intervalIntegral :
    ∃ (f : ℝ → ℝ) (G : ℂ → ℂ),
      Measurable f ∧
      (∀ t, |f t| ≤ 1) ∧
      Tendsto f atTop (𝓝 0) ∧
      ContinuousOn G {z : ℂ | 0 ≤ z.re} ∧
      DifferentiableOn ℂ G {z : ℂ | 0 < z.re} ∧
      (∀ z : ℂ, 0 < z.re → G z = ∫ t in Ici (0 : ℝ), (f t : ℂ) * cexp (-z * t)) ∧
      (∀ B : ℝ, ∃ T : ℝ, 0 ≤ T ∧ B ≤ ∫ t in (0 : ℝ)..T, f t) ∧
      (∀ L : ℂ, ¬ Tendsto (fun T : ℝ ↦ ∫ t in (0 : ℝ)..T, (f t : ℂ)) atTop (𝓝 L)) ∧
      (∀ (Ω : Set ℂ) (G' : ℂ → ℂ), IsOpen Ω → {z : ℂ | 0 ≤ z.re} ⊆ Ω →
        (∀ z : ℂ, 0 < z.re → G' z = G z) → ¬ DifferentiableOn ℂ G' Ω) := by
  obtain ⟨c, P, hc_bound, hc_zero, hP_cont, hP_diff, hP_sum, hc_unb⟩ :=
    exists_continuousOn_closedBall_hasSum_unbounded_sum_range
  set f : ℝ → ℝ := fun t ↦ c ⌊t⌋₊
  set K : ℂ → ℂ := fun z ↦ ∫ u in (0 : ℝ)..(1 : ℝ), cexp (-z * u)
  set G : ℂ → ℂ := fun z ↦ K z * P (cexp (-z))
  have hK_diff : Differentiable ℂ K := by
    simpa [K] using
      differentiable_intervalIntegral_mul_cexp_neg_mul (f := fun _ : ℝ ↦ (1 : ℂ)) (a := 0) (b := 1)
  have hmeas : Measurable f := measurable_from_nat.comp Nat.measurable_floor
  have hf_bound : ∀ t : ℝ, |f t| ≤ 1 := fun t ↦ hc_bound ⌊t⌋₊
  have hG_cont : ContinuousOn G {z : ℂ | 0 ≤ z.re} := by
    refine hK_diff.continuous.continuousOn.mul
      (hP_cont.comp (by fun_prop : Continuous fun z : ℂ ↦ cexp (-z)).continuousOn fun z hz ↦ ?_)
    rw [mem_closedBall_zero_iff, Complex.norm_exp, Complex.neg_re]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hz)
  have hG_diff : DifferentiableOn ℂ G {z : ℂ | 0 < z.re} := by
    refine hK_diff.differentiableOn.mul
      (hP_diff.comp (by fun_prop : Differentiable ℂ fun z : ℂ ↦ cexp (-z)).differentiableOn
        fun z hz ↦ ?_)
    rw [mem_ball_zero_iff, Complex.norm_exp, Complex.neg_re]
    exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hz)
  have hG_laplace : ∀ z : ℂ, 0 < z.re → G z = ∫ t in Ici (0 : ℝ), (f t : ℂ) * cexp (-z * t) := by
    intro z hz
    have hnorm : ‖cexp (-z)‖ < 1 := by
      rw [Complex.norm_exp, Complex.neg_re]
      exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hz)
    have hstep := integral_floor_div_mul_cexp_neg_mul (c := fun n ↦ (c n : ℂ)) (M := 1)
      (fun n ↦ by simpa [Complex.norm_real, Real.norm_eq_abs] using hc_bound n) one_pos hz
    simp only [div_one, ofReal_one, neg_one_mul] at hstep
    rw [hstep, (hP_sum (cexp (-z)) hnorm).tsum_eq]
  have hint_nat (N : ℕ) : ∫ t in (0 : ℝ)..(N : ℝ), f t = ∑ n ∈ Finset.range N, c n := by
    have hstep := intervalIntegral_floor_div_mul_cexp_neg_mul (c := fun n ↦ (c n : ℂ)) one_pos N 0
    simp only [mul_one, div_one, neg_zero, zero_mul, Complex.exp_zero,
      intervalIntegral.integral_const, sub_zero] at hstep
    apply Complex.ofReal_injective
    simpa [f, intervalIntegral.integral_ofReal, Complex.ofReal_sum] using hstep
  have hnot : ∀ L : ℂ, ¬ Tendsto (fun T : ℝ ↦ ∫ t in (0 : ℝ)..T, (f t : ℂ)) atTop (𝓝 L) := by
    intro L hL
    have hre : Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.range N, c n) atTop (𝓝 L.re) := by
      refine ((Complex.continuous_re.tendsto L).comp
        (hL.comp tendsto_natCast_atTop_atTop)).congr fun N ↦ ?_
      simp [intervalIntegral.integral_ofReal, hint_nat]
    obtain ⟨B, hB⟩ := hre.bddAbove_range
    obtain ⟨N, hN⟩ := hc_unb (B + 1)
    linarith [hB ⟨N, rfl⟩]
  refine ⟨f, G, hmeas, hf_bound, hc_zero.comp tendsto_nat_floor_atTop, hG_cont, hG_diff,
    hG_laplace, fun B ↦ ?_, hnot, fun Ω G' hΩ hsub heq hG' ↦ ?_⟩
  · obtain ⟨N, hN⟩ := hc_unb B
    exact ⟨N, Nat.cast_nonneg N, (hint_nat N).symm ▸ hN⟩
  · exact hnot (G' 0) (newmanLaplace_tendsto_integral
      (Complex.measurable_ofReal.comp hmeas).aestronglyMeasurable
      (fun t _ ↦ by simpa [Complex.norm_real, Real.norm_eq_abs] using hf_bound t)
      hΩ hsub hG' fun z hz ↦ (heq z hz).trans (hG_laplace z hz))

/-- Transfer of a disc-algebra power series `(c, P)` to the `b`-adic block Dirichlet series
`a n = c (Nat.log b n)` (`n ≥ 1`), giving a continuous extension to `{s | 1 ≤ s.re}` holomorphic
on `{s | 1 < s.re}`. -/
private theorem exists_continuousOn_LSeries_natLog {b : ℕ} (hb : 1 < b) {c : ℕ → ℝ} {P : ℂ → ℂ}
    (hc_bound : ∀ n, |c n| ≤ 1) (hP_cont : ContinuousOn P (closedBall 0 1))
    (hP_diff : DifferentiableOn ℂ P (ball 0 1))
    (hP_sum : ∀ w : ℂ, ‖w‖ < 1 → HasSum (fun n ↦ (c n : ℂ) * w ^ n) (P w)) :
    ∃ F : ℂ → ℂ,
      ContinuousOn F {s : ℂ | 1 ≤ s.re} ∧
      DifferentiableOn ℂ F {s : ℂ | 1 < s.re} ∧
      (∀ s : ℂ, 1 < s.re →
        LSeriesHasSum (fun n ↦ if n = 0 then (0 : ℂ) else (c (Nat.log b n) : ℂ)) s (F s)) := by
  set aC : ℕ → ℂ := fun n ↦ if n = 0 then 0 else (c (Nat.log b n) : ℂ)
  have haC_bound : ∀ n, 1 ≤ n → ‖aC n‖ ≤ 1 := fun n hn ↦ by
    simpa [aC, Nat.one_le_iff_ne_zero.mp hn, Complex.norm_real, Real.norm_eq_abs] using
      hc_bound (Nat.log b n)
  have hlogb : 0 < Real.log b := Real.log_pos (by exact_mod_cast hb)
  set K : ℂ → ℂ := fun z ↦ ∫ u in (0 : ℝ)..Real.log b, cexp (-z * u)
  set F : ℂ → ℂ := fun s ↦ K (s - 1) * P (cexp (-(Real.log b : ℂ) * (s - 1))) -
    stepCorrection aC (s - 1)
  have hK_diff : Differentiable ℂ K := by
    simpa [K] using differentiable_intervalIntegral_mul_cexp_neg_mul
      (f := fun _ : ℝ ↦ (1 : ℂ)) (a := 0) (b := Real.log b)
  have hshift_diff : Differentiable ℂ fun s : ℂ ↦ s - 1 := differentiable_id.sub_const 1
  have hre_exp (s : ℂ) : (-(Real.log b : ℂ) * (s - 1)).re = -Real.log b * (s.re - 1) := by
    rw [← Complex.ofReal_neg, Complex.re_ofReal_mul, Complex.sub_re, Complex.one_re]
  have hcorr_diff : DifferentiableOn ℂ (fun s : ℂ ↦ stepCorrection aC (s - 1)) {s : ℂ | 0 < s.re} :=
    (differentiableOn_stepCorrection haC_bound).comp hshift_diff.differentiableOn fun s hs ↦ by
      have hs' : 0 < s.re := hs
      exact (by simp only [Complex.sub_re, Complex.one_re]; linarith : -1 < (s - 1).re)
  refine ⟨F, ?_, ?_, ?_⟩
  · refine ((hK_diff.comp hshift_diff).continuous.continuousOn.mul ?_).sub
      (hcorr_diff.continuousOn.mono fun s (hs : 1 ≤ s.re) ↦ (by linarith : 0 < s.re))
    refine hP_cont.comp
      (by fun_prop : Continuous fun s : ℂ ↦ cexp (-(Real.log b : ℂ) * (s - 1))).continuousOn
      fun s (hs : 1 ≤ s.re) ↦ ?_
    rw [mem_closedBall_zero_iff, Complex.norm_exp, hre_exp]
    exact Real.exp_le_one_iff.mpr (by nlinarith)
  · refine ((hK_diff.comp hshift_diff).differentiableOn.mul ?_).sub
      (hcorr_diff.mono fun s (hs : 1 < s.re) ↦ (by linarith : 0 < s.re))
    have hexp_diff : Differentiable ℂ fun s : ℂ ↦ cexp (-(Real.log b : ℂ) * (s - 1)) := by fun_prop
    refine hP_diff.comp hexp_diff.differentiableOn fun s (hs : 1 < s.re) ↦ ?_
    rw [mem_ball_zero_iff, Complex.norm_exp, hre_exp]
    exact Real.exp_lt_one_iff.mpr (by nlinarith)
  · intro s hs
    have hz : 0 < (s - 1).re := by simp [hs]
    have hsumm : LSeriesSummable aC s :=
      LSeriesSummable_of_bounded_of_one_lt_re
        (fun n hn ↦ haC_bound n (Nat.one_le_iff_ne_zero.mpr hn)) hs
    have hnorm : ‖cexp (-(Real.log b : ℂ) * (s - 1))‖ < 1 := by
      rw [Complex.norm_exp, hre_exp]
      exact Real.exp_lt_one_iff.mpr (by nlinarith)
    have hbridge := LSeries_natLog_add_stepCorrection hb (c := fun n ↦ (c n : ℂ)) (M := 1)
      (fun n ↦ by simpa [Complex.norm_real, Real.norm_eq_abs] using hc_bound n) hz
    rw [sub_add_cancel] at hbridge
    have hFeq : LSeries aC s = F s := by
      have htsum := (hP_sum (cexp (-(Real.log b : ℂ) * (s - 1))) hnorm).tsum_eq
      simp only [F, K, aC]
      rw [← htsum, ← hbridge]
      ring
    exact hFeq ▸ hsumm.LSeriesHasSum

/-- Unboundedness of ordered harmonic partial sums of `a n = c (Nat.log b n)` from unboundedness
of `∑ k ∈ range K, c k`, using `sum_Icc_natLog_div_add_stepCorrectionTerm` and convergence of
`stepCorrection aC 0`. -/
private theorem unbounded_sum_Icc_natLog_div {b : ℕ} (hb : 1 < b) {c : ℕ → ℝ}
    (hc_bound : ∀ n, |c n| ≤ 1) (hc_unb : ∀ B : ℝ, ∃ K : ℕ, B ≤ ∑ k ∈ Finset.range K, c k) :
    ∀ B : ℝ, ∃ N : ℕ,
      B ≤ ∑ n ∈ Finset.Icc 1 N, (if n = 0 then (0 : ℝ) else c (Nat.log b n)) / (n : ℝ) := by
  set aC : ℕ → ℂ := fun n ↦ if n = 0 then 0 else (c (Nat.log b n) : ℂ)
  have haC_bound : ∀ n, 1 ≤ n → ‖aC n‖ ≤ 1 := fun n hn ↦ by
    simpa [aC, Nat.one_le_iff_ne_zero.mp hn, Complex.norm_real, Real.norm_eq_abs] using
      hc_bound (Nat.log b n)
  have hlogb : 0 < Real.log b := Real.log_pos (by exact_mod_cast hb)
  have hcorr_lim : Tendsto (fun M : ℕ ↦ (∑ n ∈ Finset.range M, stepCorrectionTerm aC n 0).re)
      atTop (𝓝 (stepCorrection aC 0).re) :=
    (Complex.continuous_re.tendsto _).comp
      (hasSum_stepCorrection (z := 0) haC_bound (by simp)).tendsto_sum_nat
  obtain ⟨C, hC⟩ := hcorr_lim.bddAbove_range
  intro B
  obtain ⟨K, hK⟩ := hc_unb ((B + C) / Real.log b)
  refine ⟨b ^ K - 1, ?_⟩
  have hre :=
    congrArg Complex.re (sum_Icc_natLog_div_add_stepCorrectionTerm hb (fun n ↦ (c n : ℂ)) K)
  have hre_lhs1 : (∑ n ∈ Finset.Icc 1 (b ^ K - 1), (c (Nat.log b n) : ℂ) / (n : ℂ)).re =
      ∑ n ∈ Finset.Icc 1 (b ^ K - 1), (if n = 0 then (0 : ℝ) else c (Nat.log b n)) / (n : ℝ) := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hn).1
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_div, Complex.ofReal_re, ite_eq_right hn0]
  have hre_rhs : ((Real.log b : ℂ) * ∑ k ∈ Finset.range K, (c k : ℂ)).re =
      Real.log b * ∑ k ∈ Finset.range K, c k := by
    rw [← Complex.ofReal_sum, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [Complex.add_re, hre_lhs1, hre_rhs] at hre
  have hcorr_le : (∑ n ∈ Finset.range (b ^ K), stepCorrectionTerm aC n 0).re ≤ C :=
    hC ⟨b ^ K, rfl⟩
  have hBC : B + C ≤ Real.log b * ∑ k ∈ Finset.range K, c k := by
    have := (div_le_iff₀ hlogb).mp hK
    linarith
  linarith

/-- **Continuous boundary values do not suffice for bounded Dirichlet series at `s = 1`.**
There exist real coefficients `a : ℕ → ℝ` with `a 0 = 0`, `|a n| ≤ 1`, `a n → 0`, and vanishing
Cesàro mean `x⁻¹ * ∑ n ∈ Icc 1 ⌊x⌋₊, a n → 0`, together with a function `F : ℂ → ℂ` continuous on
the closed half-plane `1 ≤ re s` and holomorphic on `1 < re s` satisfying
`LSeriesHasSum (fun n ↦ (a n : ℂ)) s (F s)` for `1 < re s`, such that:

* the ordered harmonic partial sums `∑ n ∈ Icc 1 N, a n / n` are unbounded above and therefore
  converge to no limit `L : ℂ` as `N → ∞`;
* `F` admits no holomorphic continuation to any open neighbourhood of `{s | 1 ≤ s.re}`.

In particular, continuous boundary data on `re s = 1`—even alongside the vanishing mean value of
Wiener–Ikehara—cannot replace the open-neighbourhood analytic continuation in
`boundedDirichlet_tendsto_ordered_at_one`. -/
theorem exists_bounded_continuousOn_LSeries_not_tendsto_sum_Icc_div :
    ∃ (a : ℕ → ℝ) (F : ℂ → ℂ),
      a 0 = 0 ∧
      (∀ n, |a n| ≤ 1) ∧
      Tendsto a atTop (𝓝 0) ∧
      Tendsto (fun x : ℝ ↦ x⁻¹ * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n) atTop (𝓝 0) ∧
      ContinuousOn F {s : ℂ | 1 ≤ s.re} ∧
      DifferentiableOn ℂ F {s : ℂ | 1 < s.re} ∧
      (∀ s : ℂ, 1 < s.re → LSeriesHasSum (fun n ↦ (a n : ℂ)) s (F s)) ∧
      (∀ B : ℝ, ∃ N : ℕ, B ≤ ∑ n ∈ Finset.Icc 1 N, a n / (n : ℝ)) ∧
      (∀ L : ℂ, ¬ Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.Icc 1 N, (a n : ℂ) / (n : ℂ))
        atTop (𝓝 L)) ∧
      (∀ (Ω : Set ℂ) (F' : ℂ → ℂ), IsOpen Ω → {s : ℂ | 1 ≤ s.re} ⊆ Ω →
        (∀ s : ℂ, 1 < s.re → F' s = F s) → ¬ DifferentiableOn ℂ F' Ω) := by
  obtain ⟨c, P, hc_bound, hc_zero, hP_cont, hP_diff, hP_sum, hc_unb⟩ :=
    exists_continuousOn_closedBall_hasSum_unbounded_sum_range
  set a : ℕ → ℝ := fun n ↦ if n = 0 then 0 else c (Nat.log 2 n)
  have haC_eq : (fun n ↦ (a n : ℂ)) = fun n ↦ if n = 0 then 0 else (c (Nat.log 2 n) : ℂ) := by
    ext n; by_cases hn : n = 0 <;> simp [a, hn]
  have ha0 : a 0 = 0 := by simp [a]
  have ha_bound : ∀ n, |a n| ≤ 1 := fun n ↦ by
    by_cases hn : n = 0 <;> simp [a, hn, hc_bound]
  have ha_zero : Tendsto a atTop (𝓝 0) := by
    have hlog : Tendsto (Nat.log 2) atTop atTop :=
      tendsto_atTop_atTop.mpr fun K ↦ ⟨2 ^ K, fun _ hn ↦ Nat.le_log_of_pow_le one_lt_two hn⟩
    refine (hc_zero.comp hlog).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp [a, Nat.one_le_iff_ne_zero.mp hn]
  have hmean : Tendsto (fun x : ℝ ↦ x⁻¹ * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n) atTop (𝓝 0) := by
    have hces : Tendsto (fun x : ℝ ↦ ((⌊x⌋₊ + 1 : ℕ) : ℝ)⁻¹ * ∑ n ∈ Finset.range (⌊x⌋₊ + 1), a n)
        atTop (𝓝 0) :=
      ha_zero.cesaro.comp ((tendsto_add_atTop_nat 1).comp tendsto_nat_floor_atTop)
    have hratio : Tendsto (fun x : ℝ ↦ ((⌊x⌋₊ + 1 : ℕ) : ℝ) / x) atTop (𝓝 1) := by
      simpa only [add_zero] using
        (tendsto_nat_floor_div_atTop (R := ℝ) |>.add tendsto_inv_atTop_zero).congr fun x ↦ by
          push_cast; rw [add_div, one_div]
    have hprod : Tendsto (fun x : ℝ ↦ (((⌊x⌋₊ + 1 : ℕ) : ℝ) / x) *
        (((⌊x⌋₊ + 1 : ℕ) : ℝ)⁻¹ * ∑ n ∈ Finset.range (⌊x⌋₊ + 1), a n)) atTop (𝓝 0) := by
      simpa using hratio.mul hces
    refine hprod.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hsum_eq : ∑ n ∈ Finset.range (⌊x⌋₊ + 1), a n = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n := by
      rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos _), ha0, zero_add,
        zero_add, Nat.succ_eq_add_one, Finset.Ico_add_one_right_eq_Icc]
    have hpos : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
    rw [hsum_eq]
    field_simp [hpos, hx.ne']
  obtain ⟨F, hF_cont, hF_diff, hF_series⟩ :=
    exists_continuousOn_LSeries_natLog one_lt_two hc_bound hP_cont hP_diff hP_sum
  rw [← haC_eq] at hF_series
  have hunb := unbounded_sum_Icc_natLog_div one_lt_two hc_bound hc_unb
  have hnot : ∀ L : ℂ, ¬ Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.Icc 1 N, (a n : ℂ) / (n : ℂ))
      atTop (𝓝 L) := by
    intro L hL
    have hre : Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.Icc 1 N, a n / (n : ℝ)) atTop (𝓝 L.re) := by
      refine ((Complex.continuous_re.tendsto L).comp hL).congr fun N ↦ ?_
      simp only [Function.comp_apply, Complex.re_sum]
      refine Finset.sum_congr rfl fun n _ ↦ ?_
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_div, Complex.ofReal_re]
    obtain ⟨B, hB⟩ := hre.bddAbove_range
    obtain ⟨N, hN⟩ := hunb (B + 1)
    linarith [hB ⟨N, rfl⟩]
  refine ⟨a, F, ha0, ha_bound, ha_zero, hmean, hF_cont, hF_diff, hF_series, hunb, hnot,
    fun Ω F' hΩ hsub heq hF' ↦ ?_⟩
  exact hnot (F' 1) (boundedDirichlet_tendsto_ordered_at_one
    (fun n _ ↦ by simpa [Complex.norm_real, Real.norm_eq_abs] using ha_bound n)
    hΩ hsub hF' fun s hs ↦ (heq s hs).symm ▸ hF_series s hs)

end TauCeti.LSeries
