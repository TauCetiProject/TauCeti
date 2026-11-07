/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import Mathlib.Analysis.Complex.BorelCaratheodory
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.SpecificLimits.RCLike

/-!
# Polynomial growth of entire logarithms

For an entire `H`, an upper bound `Complex.exp(H(z)) = O(Complex.exp(‖z‖^p))` with `p ≥ 0` forces
`H(z) = O(‖z‖^p)`. An upper bound on the real part therefore controls the entire complex
function at the same power. This supplies the growth transfer needed to identify the
exponential factor in Hadamard's theorem.
-/

public section

open Complex Filter Bornology Topology Asymptotics

/-- An entire logarithm inherits a polynomial norm bound from an exponential norm bound
on its exponential, for every nonnegative real exponent. -/
theorem Differentiable.isBigO_of_cexp_isBigO {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    {p : ℝ} (hp : 0 ≤ p)
    (h : (fun z ↦ Complex.exp (H z)) =O[cobounded ℂ] (fun z ↦ Real.exp (‖z‖ ^ p))) :
    H =O[cobounded ℂ] (fun z ↦ ‖z‖ ^ p) := by
  obtain ⟨C, hC, hb⟩ := h.exists_pos
  obtain ⟨L, _, hL⟩ := Filter.hasBasis_cobounded_norm.mem_iff.mp hb.bound
  have hexp : Differentiable ℂ (fun z ↦ Complex.exp (H z)) := hH.cexp
  -- Maximum modulus extends the large-circle bound to the enclosed disk.
  have hreal (R : ℝ) (hRL : L ≤ R) (w : ℂ) (hw : w ∈ Metric.ball 0 R) :
      (H w).re ≤ Real.log C + R ^ p := by
    have he : ‖Complex.exp (H w)‖ ≤ C * Real.exp (R ^ p) := by
      apply Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball
        ⟨hexp.differentiableOn, hexp.continuous.continuousOn⟩ _ (subset_closure hw)
      intro z hz
      have hzR : ‖z‖ = R := by
        simpa only [Metric.mem_sphere, dist_zero_right] using Metric.frontier_ball_subset_sphere hz
      have hzL : L ≤ ‖z‖ := by rw [hzR]; exact hRL
      simpa only [Set.mem_ofPred_eq, Real.norm_eq_abs, Real.abs_exp, hzR] using hL hzL
    have heq : C * Real.exp (R ^ p) = Real.exp (Real.log C + R ^ p) := by
      rw [Real.exp_add, Real.exp_log hC]
    rw [norm_exp, heq] at he
    exact Real.exp_le_exp.mp he
  -- Borel–Carathéodory on a disk twice as large controls the full complex norm.
  let K : ℝ := 2 * (|Real.log C| + 1) + 3 * ‖H 0‖ + 2 * 2 ^ p
  apply Asymptotics.IsBigO.of_bound K
  filter_upwards [eventually_cobounded_le_norm (max L 1)] with z hz
  have hz1 : 1 ≤ ‖z‖ := (le_max_right _ _).trans hz
  have hz0 : 0 < ‖z‖ := zero_lt_one.trans_le hz1
  have hzL : L ≤ 2 * ‖z‖ := by have := (le_max_left _ _).trans hz; linarith
  let M : ℝ := |Real.log C| + (2 * ‖z‖) ^ p + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hMbound : Set.MapsTo H (Metric.ball 0 (2 * ‖z‖)) {w | w.re ≤ M} := by
    intro w hw
    have hr := hreal _ hzL w hw
    have habs := le_abs_self (Real.log C)
    rw [Set.mem_ofPred_eq]
    dsimp [M]
    linarith
  have hball : z ∈ Metric.ball 0 (2 * ‖z‖) := by
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have hbc := Complex.borelCaratheodory hM hH.differentiableOn hMbound
    (by positivity : 0 < 2 * ‖z‖) hball
  have hden : 2 * ‖z‖ - ‖z‖ = ‖z‖ := by ring
  rw [hden, mul_div_cancel_right₀ _ hz0.ne'] at hbc
  have hlast : ‖H 0‖ * (2 * ‖z‖ + ‖z‖) / ‖z‖ = 3 * ‖H 0‖ := by
    field_simp
    ring
  rw [hlast] at hbc
  have hpow : 1 ≤ ‖z‖ ^ p := Real.one_le_rpow hz1 hp
  have hbc' : ‖H z‖ ≤ 2 * (|Real.log C| + 1) + 3 * ‖H 0‖ +
      (2 * 2 ^ p) * ‖z‖ ^ p := by
    dsimp [M] at hbc
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (norm_nonneg z)] at hbc
    nlinarith
  have hconst : 0 ≤ 2 * (|Real.log C| + 1) + 3 * ‖H 0‖ := by positivity
  have hm := mul_le_mul_of_nonneg_left hpow hconst
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg z) p)]
  dsimp [K]
  nlinarith

