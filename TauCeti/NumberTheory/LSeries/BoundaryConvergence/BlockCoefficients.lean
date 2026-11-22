/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.NumberTheory.LSeries.Basic
public import TauCeti.NumberTheory.LSeries.BoundaryConvergence.StepCorrection
import TauCeti.Analysis.LaplaceTransform.ExponentialStep
import TauCeti.Analysis.LaplaceTransform.UniformStep
import TauCeti.NumberTheory.LSeries.BoundaryConvergence.LaplaceBridge
import TauCeti.NumberTheory.LSeries.Term

/-!
# Block-constant Dirichlet series and uniform step transforms

For an integer base `b > 1` and a sequence `c : ℕ → ℂ`, the `b`-adic block-constant sequence
`a n = c (Nat.log b n)` (`n ≥ 1`, `a 0 = 0`) satisfies `Nat.log b ⌊exp t⌋₊ = ⌊t / log b⌋₊`
for `0 ≤ t` (`Real.natFloor_logb_eq_natLog_natFloor`). Combining this with the integral identity
`TauCeti.integral_floor_exp_natLog_mul_cexp_neg_mul`:

* when `c` is bounded and `0 < re z`, `LSeries a (z + 1) + stepCorrection a z` equals
  `(∫ u in 0..log b, exp (-z * u)) * ∑' k, c k * exp (-log b * z) ^ k`
  (`LSeries_natLog_add_stepCorrection`);
* at cutoffs `b ^ K - 1`, the ordered harmonic partial sum plus the step correction at `z = 0`
  equals `log b * ∑ k ∈ range K, c k` (`sum_Icc_natLog_div_add_stepCorrectionTerm`);
* a disc-algebra power series `(c, P)` transfers directly to a continuous boundary extension of
  `LSeries a` on `1 ≤ re s` (`exists_continuousOn_LSeries_natLog`), while unbounded partial sums
  `∑ k ∈ range K, c k` yield unbounded real harmonic sums (`unbounded_sum_Icc_natLog_div`).

## Main results

* `TauCeti.LSeries.LSeries_natLog_add_stepCorrection`: Laplace–Dirichlet bridge for block
  coefficients.
* `TauCeti.LSeries.sum_Icc_natLog_div_add_stepCorrectionTerm`: partial-sum identity at powers
  of `b`.
* `TauCeti.LSeries.exists_continuousOn_LSeries_natLog`: disc-algebra transfer to `1 ≤ re s`.
* `TauCeti.LSeries.re_sum_ofReal_div_natCast`: real part of a finite harmonic sum with real
  coefficients.
* `TauCeti.LSeries.unbounded_sum_Icc_natLog_div`: unboundedness of real ordered harmonic sums.
-/

public section

open Filter MeasureTheory Metric Set Complex
open scoped Topology Interval

namespace TauCeti.LSeries

private theorem LSeries_natLog_add_stepCorrection_eq_integral (b : ℕ) {c : ℕ → ℂ} {M : ℝ}
    (hbound : ∀ n, ‖c n‖ ≤ M) {z : ℂ} (hz : 0 < z.re) :
    LSeries (fun n ↦ if n = 0 then 0 else c (Nat.log b n)) (z + 1) +
        stepCorrection (fun n ↦ if n = 0 then 0 else c (Nat.log b n)) z =
      ∫ t in Ici (0 : ℝ), c ⌊t / Real.log b⌋₊ * cexp (-z * t) := by
  have habound : ∀ n, 1 ≤ n → ‖(if n = 0 then 0 else c (Nat.log b n))‖ ≤ M := by
    intro n hn
    simp [Nat.one_le_iff_ne_zero.mp hn, hbound]
  rw [← integral_floor_exp_mul_cexp_neg_mul habound hz,
    integral_floor_exp_natLog_mul_cexp_neg_mul b c z]

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
  have hlogb : 0 < Real.log b := Real.log_pos (by exact_mod_cast hb)
  rw [LSeries_natLog_add_stepCorrection_eq_integral b hbound hz,
    integral_floor_div_mul_cexp_neg_mul hbound hlogb hz]

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
    exact ite_floor_exp_natLog_eq b c ht.1
  have hterm : ∑ n ∈ Finset.range (b ^ K), LSeries.term a 1 n =
      ∑ n ∈ Finset.Icc 1 (b ^ K - 1), c (Nat.log b n) / (n : ℂ) := by
    rw [← Nat.sub_add_cancel hpow_pos, sum_range_add_one_LSeries_term_one]
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    simp [a, Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hn).1]
  rw [← hterm, ← hL, hint_eq, hR]
  simp [Complex.real_smul]

/-- **Transfer of a disc-algebra power series to a `b`-adic block Dirichlet series.** Given an
integer base `b > 1` and a bounded sequence `c : ℕ → ℂ` whose power series `∑' n, c n * w ^ n`
has a continuous extension `P` to the closed unit disc `‖w‖ ≤ 1`, the block Dirichlet series with
coefficients `a n = c (Nat.log b n)` (`n ≥ 1`, `a 0 = 0`) admits a function `F : ℂ → ℂ`
continuous on `{s | 1 ≤ s.re}` and holomorphic on `{s | 1 < s.re}` satisfying
`LSeriesHasSum a s (F s)` for `1 < s.re`. -/
theorem exists_continuousOn_LSeries_natLog {b : ℕ} (hb : 1 < b) {c : ℕ → ℂ} {M : ℝ} {P : ℂ → ℂ}
    (hc_bound : ∀ n, ‖c n‖ ≤ M) (hP_cont : ContinuousOn P (closedBall 0 1))
    (hP_sum : ∀ w : ℂ, ‖w‖ < 1 → HasSum (fun n ↦ c n * w ^ n) (P w)) :
    ∃ F : ℂ → ℂ,
      ContinuousOn F {s : ℂ | 1 ≤ s.re} ∧
      DifferentiableOn ℂ F {s : ℂ | 1 < s.re} ∧
      (∀ s : ℂ, 1 < s.re →
        LSeriesHasSum (fun n ↦ if n = 0 then (0 : ℂ) else c (Nat.log b n)) s (F s)) := by
  set a : ℕ → ℂ := fun n ↦ if n = 0 then 0 else c (Nat.log b n)
  have ha_bound : ∀ n, 1 ≤ n → ‖a n‖ ≤ M := fun n hn ↦ by
    simpa [a, Nat.one_le_iff_ne_zero.mp hn] using hc_bound (Nat.log b n)
  have hlogb : 0 < Real.log b := Real.log_pos (by exact_mod_cast hb)
  obtain ⟨G, hG_cont, hG_diff, hG_eq⟩ :=
    exists_continuousOn_integral_floor_div_mul_cexp_neg_mul hc_bound hlogb hP_cont hP_sum
  set F : ℂ → ℂ := fun s ↦ G (s - 1) - stepCorrection a (s - 1)
  have hshift_diff : Differentiable ℂ fun s : ℂ ↦ s - 1 := differentiable_id.sub_const 1
  have hcorr_diff : DifferentiableOn ℂ (fun s : ℂ ↦ stepCorrection a (s - 1)) {s : ℂ | 0 < s.re} :=
    (differentiableOn_stepCorrection ha_bound).comp hshift_diff.differentiableOn
      fun s hs ↦ by
        simp only [mem_ofPred_eq, Complex.sub_re, Complex.one_re] at hs ⊢
        linarith
  have hz : ∀ s ∈ {s : ℂ | 1 < s.re}, 0 < (s - 1).re := fun s hs ↦ by
    simp only [mem_ofPred_eq, Complex.sub_re, Complex.one_re] at hs ⊢
    exact sub_pos.mpr hs
  refine ⟨F, ?_, ?_, ?_⟩
  · refine (hG_cont.comp (hshift_diff.continuous.continuousOn (s := {s : ℂ | 1 ≤ s.re}))
        fun s hs ↦ ?_).sub
      (hcorr_diff.continuousOn.mono fun s hs ↦ by
        simp only [mem_ofPred_eq] at hs ⊢
        linarith)
    simp only [mem_ofPred_eq, Complex.sub_re, Complex.one_re] at hs ⊢
    exact sub_nonneg.mpr hs
  · refine (hG_diff.comp (hshift_diff.differentiableOn (s := {s : ℂ | 1 < s.re})) hz).sub
      (hcorr_diff.mono fun s hs ↦ by
        simp only [mem_ofPred_eq] at hs ⊢
        linarith)
  · intro s hs
    have hzs := hz s hs
    have hsumm : LSeriesSummable a s :=
      LSeriesSummable_of_bounded_of_one_lt_re
        (fun n hn ↦ ha_bound n (Nat.one_le_iff_ne_zero.mpr hn)) hs
    have hFeq : LSeries a s = F s := by
      have hlap := LSeries_natLog_add_stepCorrection_eq_integral b hc_bound hzs
      rw [sub_add_cancel, ← hG_eq (s - 1) hzs] at hlap
      exact eq_sub_of_add_eq hlap
    exact hFeq ▸ hsumm.LSeriesHasSum

/-- The real part of a finite harmonic sum with real coefficients is the corresponding real
harmonic sum. -/
theorem re_sum_ofReal_div_natCast (s : Finset ℕ) (f : ℕ → ℝ) :
    (∑ n ∈ s, (f n : ℂ) / (n : ℂ)).re = ∑ n ∈ s, f n / (n : ℝ) := by
  simp only [Complex.re_sum, Complex.div_natCast_re, Complex.ofReal_re]

/-- **Unboundedness of ordered harmonic partial sums for `b`-adic block coefficients.** For an
integer base `b > 1` and a bounded real sequence `c : ℕ → ℝ` whose partial sums `∑ k ∈ range K, c k`
are unbounded above, the real ordered harmonic partial sums `∑ n ∈ Icc 1 N, c (Nat.log b n) / n`
are also unbounded above. -/
theorem unbounded_sum_Icc_natLog_div {b : ℕ} (hb : 1 < b) {c : ℕ → ℝ} {M : ℝ}
    (hc_bound : ∀ n, |c n| ≤ M) (hc_unb : ∀ B : ℝ, ∃ K : ℕ, B ≤ ∑ k ∈ Finset.range K, c k) :
    ∀ B : ℝ, ∃ N : ℕ, B ≤ ∑ n ∈ Finset.Icc 1 N, c (Nat.log b n) / (n : ℝ) := by
  set aC : ℕ → ℂ := fun n ↦ if n = 0 then 0 else (c (Nat.log b n) : ℂ)
  have haC_bound : ∀ n, 1 ≤ n → ‖aC n‖ ≤ M := fun n hn ↦ by
    simpa [aC, Nat.one_le_iff_ne_zero.mp hn, Complex.norm_real, Real.norm_eq_abs] using
      hc_bound (Nat.log b n)
  have hlogb : 0 < Real.log b := Real.log_pos (by exact_mod_cast hb)
  have hcorr_lim : Tendsto (fun m : ℕ ↦ (∑ n ∈ Finset.range m, stepCorrectionTerm aC n 0).re)
      atTop (𝓝 (stepCorrection aC 0).re) :=
    (Complex.continuous_re.tendsto _).comp
      (hasSum_stepCorrection (z := 0) haC_bound (by simp)).tendsto_sum_nat
  obtain ⟨C, hC⟩ := hcorr_lim.bddAbove_range
  intro B
  obtain ⟨K, hK⟩ := hc_unb ((B + C) / Real.log b)
  refine ⟨b ^ K - 1, ?_⟩
  have hre :=
    congrArg Complex.re (sum_Icc_natLog_div_add_stepCorrectionTerm hb (fun n ↦ (c n : ℂ)) K)
  have hre_rhs : ((Real.log b : ℂ) * ∑ k ∈ Finset.range K, (c k : ℂ)).re =
      Real.log b * ∑ k ∈ Finset.range K, c k := by
    rw [← Complex.ofReal_sum, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [Complex.add_re, re_sum_ofReal_div_natCast, Complex.re_sum, hre_rhs] at hre
  have hcorr_le : (∑ n ∈ Finset.range (b ^ K), stepCorrectionTerm aC n 0).re ≤ C :=
    hC ⟨b ^ K, rfl⟩
  simp only [Complex.re_sum] at hcorr_le
  dsimp only [aC] at hcorr_le
  have hBC : B + C ≤ Real.log b * ∑ k ∈ Finset.range K, c k := by
    rw [mul_comm]
    exact (div_le_iff₀ hlogb).mp hK
  linarith

end TauCeti.LSeries
