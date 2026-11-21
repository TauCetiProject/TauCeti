/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import TauCeti.Analysis.Complex.PowerSeries.Fejer
import TauCeti.Analysis.LaplaceTransform.UniformStep
import TauCeti.NumberTheory.LSeries.BoundaryConvergence.BlockCoefficients
import TauCeti.NumberTheory.LSeries.BoundaryConvergence.Endpoint

/-!
# Continuous boundary values do not force Dirichlet convergence at `s = 1`

The bounded Dirichlet endpoint theorem (`boundedDirichlet_tendsto_ordered_at_one`) requires a
holomorphic continuation across an open neighbourhood of the closed half-plane `1 ≤ re s`. This
file proves that continuity up to the boundary line `re s = 1`—even together with holomorphy on
`1 < re s`, vanishing coefficients `a n → 0`, and vanishing Cesàro mean—does not suffice.

Taking Fejér's 1911 disc-algebra counterexample `(c, P)`
(`TauCeti.exists_continuousOn_closedBall_hasSum_unbounded_sum_range`) with base `b = 2` and
setting `a n = c (Nat.log 2 n)` (`n ≥ 1`, `a 0 = 0`), the bridge identities in
`TauCeti.NumberTheory.LSeries.BoundaryConvergence.BlockCoefficients` together with the uniform
step transfer (`TauCeti.exists_continuousOn_integral_floor_div_mul_cexp_neg_mul`) produce a function
`F` continuous on `1 ≤ re s` and holomorphic on `1 < re s` agreeing with `LSeries a s`, while the
ordered harmonic partial sums `∑ n ∈ Icc 1 N, a n / n` are unbounded above and therefore converge to
no limit `L : ℂ` (`exists_bounded_continuousOn_LSeries_not_tendsto_sum_Icc_div`).
-/

public section

open Filter MeasureTheory Set Metric Complex
open scoped Topology

namespace TauCeti.LSeries

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
  have hc_norm : ∀ n, ‖(c n : ℂ)‖ ≤ 1 := fun n ↦ by
    simpa [Complex.norm_real, Real.norm_eq_abs] using hc_bound n
  have haC_bound : ∀ n, 1 ≤ n → ‖aC n‖ ≤ 1 := fun n hn ↦ by
    simpa [aC, Nat.one_le_iff_ne_zero.mp hn] using hc_norm (Nat.log b n)
  have hlogb : 0 < Real.log b := Real.log_pos (by exact_mod_cast hb)
  obtain ⟨G, hG_cont, hG_diff, hG_eq⟩ :=
    exists_continuousOn_integral_floor_div_mul_cexp_neg_mul hc_norm hlogb hP_cont hP_diff hP_sum
  set F : ℂ → ℂ := fun s ↦ G (s - 1) - stepCorrection aC (s - 1)
  have hshift_diff : Differentiable ℂ fun s : ℂ ↦ s - 1 := differentiable_id.sub_const 1
  have hcorr_diff : DifferentiableOn ℂ (fun s : ℂ ↦ stepCorrection aC (s - 1)) {s : ℂ | 0 < s.re} :=
    (differentiableOn_stepCorrection haC_bound).comp hshift_diff.differentiableOn
      fun s (hs : 0 < s.re) ↦
        (by simp only [Complex.sub_re, Complex.one_re]; linarith : -1 < (s - 1).re)
  refine ⟨F, ?_, ?_, ?_⟩
  · refine (hG_cont.comp (hshift_diff.continuous.continuousOn (s := {s : ℂ | 1 ≤ s.re}))
        fun s hs ↦ ?_).sub
      (hcorr_diff.continuousOn.mono fun s (hs : 1 ≤ s.re) ↦ (by linarith : 0 < s.re))
    change 0 ≤ (s - 1).re
    simp only [Complex.sub_re, Complex.one_re]
    linarith [show (1 : ℝ) ≤ s.re from hs]
  · refine (hG_diff.comp (hshift_diff.differentiableOn (s := {s : ℂ | 1 < s.re}))
        fun s hs ↦ ?_).sub
      (hcorr_diff.mono fun s (hs : 1 < s.re) ↦ (by linarith : 0 < s.re))
    change 0 < (s - 1).re
    simp only [Complex.sub_re, Complex.one_re]
    linarith [show (1 : ℝ) < s.re from hs]
  · intro s hs
    have hz : 0 < (s - 1).re := by simp [hs]
    have hsumm : LSeriesSummable aC s :=
      LSeriesSummable_of_bounded_of_one_lt_re
        (fun n hn ↦ haC_bound n (Nat.one_le_iff_ne_zero.mpr hn)) hs
    have hbridge := LSeries_natLog_add_stepCorrection hb hc_norm hz
    rw [sub_add_cancel] at hbridge
    have hFeq : LSeries aC s = F s := by
      have hG_val : G (s - 1) = (∫ u in (0 : ℝ)..Real.log b, cexp (-(s - 1) * u)) *
          ∑' k, (c k : ℂ) * cexp (-(Real.log b : ℂ) * (s - 1)) ^ k := by
        rw [hG_eq _ hz, integral_floor_div_mul_cexp_neg_mul hc_norm hlogb hz]
      simp only [F, aC]
      rw [hG_val, ← hbridge]
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

/-- A real sequence with `a 0 = 0` and `a n → 0` has vanishing real-cutoff Cesàro mean
`x⁻¹ * ∑ n ∈ Icc 1 ⌊x⌋₊, a n → 0`. -/
private theorem tendsto_inv_mul_sum_Icc_floor_zero {a : ℕ → ℝ} (ha0 : a 0 = 0)
    (ha : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun x : ℝ ↦ x⁻¹ * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n) atTop (𝓝 0) := by
  have hces : Tendsto (fun x : ℝ ↦ ((⌊x⌋₊ + 1 : ℕ) : ℝ)⁻¹ * ∑ n ∈ Finset.range (⌊x⌋₊ + 1), a n)
      atTop (𝓝 0) :=
    ha.cesaro.comp ((tendsto_add_atTop_nat 1).comp tendsto_nat_floor_atTop)
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
    rw [Finset.sum_range_eq_add_Ico _ (Nat.succ_pos _), ha0, zero_add, Nat.succ_eq_add_one,
      Finset.Ico_add_one_right_eq_Icc]
  have hpos : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
  rw [hsum_eq]
  field_simp [hpos, hx.ne']

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
  have hmean := tendsto_inv_mul_sum_Icc_floor_zero ha0 ha_zero
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
