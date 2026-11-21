/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.QPochhammer
public import TauCeti.NumberTheory.ModularForms.QExpansion.Basic
public import TauCeti.RingTheory.PowerSeries.QPochhammer
import TauCeti.NumberTheory.ModularForms.QExpansion.BigO

/-!
# `q`-expansions of shifted `q`-Pochhammer products

For `h > 0`, `0 < N`, and `c : ℕ`, the cusp function of `τ ↦ qPochhammerFun N c w (𝕢 h τ)` agrees
near `0` with `qPochhammerFun N c w` (`cuspFunction_qPochhammerFun_eventuallyEq`,
`analyticAt_cuspFunction_qPochhammerFun`). Together with the partial product split
`qExpansion_qPochhammerFun_eq_prod_range_mul`, this gives `qExpansion_qPochhammerFun`: the
`q`-expansion equals `TauCeti.qPochhammerSeries N c w`.
-/

public noncomputable section

open UpperHalfPlane Filter Topology

namespace TauCeti.UpperHalfPlane

local notation "𝕢" => Function.Periodic.qParam

variable {h : ℝ}

/-- Near `0`, the cusp function of `τ ↦ qPochhammerFun N c w (𝕢 h τ)` agrees with
`qPochhammerFun N c w` for `0 < h` and `0 < N`. -/
theorem cuspFunction_qPochhammerFun_eventuallyEq (hh : 0 < h) {N : ℕ} (hN : 0 < N)
    (c : ℕ) (w : ℂ) :
    cuspFunction h (fun τ : ℍ ↦ qPochhammerFun N c w (𝕢 h τ)) =ᶠ[𝓝 0] qPochhammerFun N c w := by
  refine cuspFunction_eventuallyEq_nhds_of_continuousAt ?_
    (analyticAt_qPochhammerFun hN c w).continuousAt
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)] with q hq hqn
  have hq' : q ≠ 0 := Set.mem_compl_singleton_iff.mp hq
  rw [cuspFunction_of_ne_zero hq',
    ofComplex_apply_of_im_pos (Function.Periodic.im_invQParam_pos_of_norm_lt_one hh
      (mem_ball_zero_iff.mp hqn) hq'),
    Function.Periodic.qParam_right_inv hh.ne' hq']

/-- For `0 < h` and `0 < N`, the cusp function of `τ ↦ qPochhammerFun N c w (𝕢 h τ)` is analytic
at `0`. -/
theorem analyticAt_cuspFunction_qPochhammerFun (hh : 0 < h) {N : ℕ} (hN : 0 < N) (c : ℕ) (w : ℂ) :
    AnalyticAt ℂ (cuspFunction h fun τ : ℍ ↦ qPochhammerFun N c w (𝕢 h τ)) 0 :=
  (analyticAt_qPochhammerFun hN c w).congr (cuspFunction_qPochhammerFun_eventuallyEq hh hN c w).symm

/-- For `0 < h` and `0 < N`, splitting off the first `m` factors of `qPochhammerFun N c w (𝕢 h τ)`
in `qExpansion`. -/
theorem qExpansion_qPochhammerFun_eq_prod_range_mul (hh : 0 < h) {N : ℕ} (hN : 0 < N)
    (c m : ℕ) (w : ℂ) :
    qExpansion h (fun τ : ℍ ↦ qPochhammerFun N c w (𝕢 h τ)) =
      (∏ n ∈ Finset.range m, (1 - PowerSeries.C w * PowerSeries.X ^ (N * n + c))) *
        qExpansion h (fun τ : ℍ ↦ qPochhammerFun N (N * m + c) w (𝕢 h τ)) := by
  induction m generalizing c with
  | zero => simp
  | succ m ih =>
    have hfun : (fun τ : ℍ ↦ qPochhammerFun N c w (𝕢 h τ)) =
        (fun τ : ℍ ↦ 1 - w * 𝕢 h τ ^ c) * fun τ : ℍ ↦ qPochhammerFun N (N + c) w (𝕢 h τ) :=
      funext fun τ ↦
        qPochhammerFun_eq_one_sub_mul hN c w (Function.Periodic.norm_qParam_lt_one hh τ.im_pos)
    have hshift (n : ℕ) : N * n + (N + c) = N * (n + 1) + c := by
      rw [Nat.mul_succ]
      ring
    rw [hfun, _root_.UpperHalfPlane.qExpansion_mul
      (analyticAt_cuspFunction_one_sub_mul_qParam_pow h c w)
      (analyticAt_cuspFunction_qPochhammerFun hh hN _ w),
      qExpansion_one_sub_mul_qParam_pow hh c w, ih (N + c)]
    simp only [hshift, Finset.prod_range_succ', mul_zero, zero_add]
    ring

/-- **The `q`-expansion of a shifted `q`-Pochhammer product.** For `0 < h` and `0 < N`, the
`q`-expansion of `τ ↦ ∏_{n ≥ 0} (1 - w 𝕢 h τ^{N n + c})` equals the formal power series
`qPochhammerSeries N c w`. -/
theorem qExpansion_qPochhammerFun (hh : 0 < h) {N : ℕ} (hN : 0 < N) (c : ℕ) (w : ℂ) :
    qExpansion h (fun τ : ℍ ↦ qPochhammerFun N c w (𝕢 h τ)) = qPochhammerSeries N c w := by
  ext m
  set c' := N * (m + 1) + c
  have hc' : m < c' := by have := Nat.mul_le_mul_right (m + 1) hN; omega
  have han1 : AnalyticAt ℂ (cuspFunction h (1 : ℍ → ℂ)) 0 := by
    rw [Pi.one_def]; exact analyticAt_cuspFunction_const h 1
  have hanP := analyticAt_cuspFunction_qPochhammerFun hh hN c' w
  have hzero : ∀ k < c',
      (qExpansion h ((fun τ : ℍ ↦ qPochhammerFun N c' w (𝕢 h τ)) - 1)).coeff k = 0 := by
    refine (cuspFunction_isBigO_pow_iff_qExpansion_coeff_eq_zero
      (analyticAt_cuspFunction_sub hanP han1)).mp ?_
    refine (isBigO_qPochhammerFun_sub_one hN (by omega) w).congr' ?_ EventuallyEq.rfl
    have hsub := _root_.UpperHalfPlane.cuspFunction_sub (h := h) hanP.continuousAt han1.continuousAt
    filter_upwards [cuspFunction_qPochhammerFun_eventuallyEq hh hN c' w] with z hz₁
    rw [hsub, Pi.sub_apply, cuspFunction_one, Pi.one_apply, hz₁]
  have hcoeff (k : ℕ) (hk : k < c') :
      (qExpansion h (fun τ : ℍ ↦ qPochhammerFun N c' w (𝕢 h τ))).coeff k =
        (1 : PowerSeries ℂ).coeff k := by
    have h := hzero k hk
    rwa [_root_.UpperHalfPlane.qExpansion_sub hanP han1, _root_.UpperHalfPlane.qExpansion_one,
      map_sub, sub_eq_zero] at h
  rw [qExpansion_qPochhammerFun_eq_prod_range_mul hh hN c (m + 1) w, coeff_qPochhammerSeries,
    PowerSeries.coeff_mul]
  rw [Finset.sum_congr rfl fun p hp ↦ by
    rw [hcoeff p.2 ((by have := Finset.mem_antidiagonal.mp hp; omega : p.2 ≤ m).trans_lt hc')],
    ← PowerSeries.coeff_mul, mul_one]

end TauCeti.UpperHalfPlane
