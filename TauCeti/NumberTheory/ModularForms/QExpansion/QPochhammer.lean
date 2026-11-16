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

For `h > 0`, `0 < N`, and `c : ℕ`, evaluating the analytic shifted `q`-Pochhammer product
`TauCeti.qPochhammerFun N c w (𝕢 h τ) = ∏_{n ≥ 0} (1 - w 𝕢 h τ^{N n + c})` on the upper
half-plane defines a function whose cusp function at `0` agrees near `0` with
`TauCeti.qPochhammerFun N c w`, hence is analytic at `0`.

When `0 < c`, its `q`-expansion `UpperHalfPlane.qExpansion h` equals the formal shifted
`q`-Pochhammer power series `TauCeti.qPochhammerSeries N c w`: splitting off the first `m` factors
leaves a tail `qPochhammerFun N (N * m + c) w (𝕢 h τ)` that differs from `1` by
`O(‖q‖^{N m + c})`, so its `q`-expansion coefficients of degree `≤ m` match the `m`-th partial
product.

## Main declarations

* `TauCeti.UpperHalfPlane.cuspFunction_qPochhammerFun_eventuallyEq`: near `0`, the cusp function of
  `τ ↦ qPochhammerFun N c w (𝕢 h τ)` agrees with `qPochhammerFun N c w`.
* `TauCeti.UpperHalfPlane.analyticAt_cuspFunction_qPochhammerFun`: its cusp function is analytic
  at `0`.
* `TauCeti.UpperHalfPlane.analyticAt_cuspFunction_one_sub_mul_qParam_pow` and
  `TauCeti.UpperHalfPlane.qExpansion_one_sub_mul_qParam_pow`: analyticity and `q`-expansion of a
  single factor `1 - w 𝕢 h τ ^ c`.
* `TauCeti.UpperHalfPlane.qExpansion_qPochhammerFun_eq_prod_range_mul`: splitting off the first
  `m` factors in `qExpansion`.
* `TauCeti.UpperHalfPlane.qExpansion_qPochhammerFun`: for `0 < h`, `0 < N`, and `0 < c`,
  `qExpansion h (fun τ ↦ qPochhammerFun N c w (𝕢 h τ)) = qPochhammerSeries N c w`.
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
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hq
  rw [cuspFunction_of_ne_zero hq,
    ofComplex_apply_of_im_pos (Function.Periodic.im_invQParam_pos_of_norm_lt_one hh
      (mem_ball_zero_iff.mp hqn) hq),
    Function.Periodic.qParam_right_inv hh.ne' hq]

/-- For `0 < h` and `0 < N`, the cusp function of `τ ↦ qPochhammerFun N c w (𝕢 h τ)` is analytic
at `0`. -/
theorem analyticAt_cuspFunction_qPochhammerFun (hh : 0 < h) {N : ℕ} (hN : 0 < N)
    (c : ℕ) (w : ℂ) :
    AnalyticAt ℂ (cuspFunction h fun τ : ℍ ↦ qPochhammerFun N c w (𝕢 h τ)) 0 :=
  (analyticAt_qPochhammerFun hN c w).congr (cuspFunction_qPochhammerFun_eventuallyEq hh hN c w).symm

/-- The cusp function of `τ ↦ 1 - w * 𝕢 h τ ^ c` is analytic at `0`. -/
theorem analyticAt_cuspFunction_one_sub_mul_qParam_pow (h : ℝ) (c : ℕ) (w : ℂ) :
    AnalyticAt ℂ (cuspFunction h fun τ : ℍ ↦ 1 - w * 𝕢 h τ ^ c) 0 := by
  have hfun : (fun τ : ℍ ↦ 1 - w * 𝕢 h τ ^ c) = (1 : ℍ → ℂ) - w • fun τ : ℍ ↦ 𝕢 h τ ^ c :=
    funext fun τ ↦ by simp
  rw [hfun]
  exact analyticAt_cuspFunction_sub (by rw [Pi.one_def]; exact analyticAt_cuspFunction_const h 1)
    (analyticAt_cuspFunction_smul (analyticAt_cuspFunction_qParam_pow h c) w)

/-- For `0 < h`, the `q`-expansion of `τ ↦ 1 - w * 𝕢 h τ ^ c` is `1 - C w * X ^ c`. -/
theorem qExpansion_one_sub_mul_qParam_pow (hh : 0 < h) (c : ℕ) (w : ℂ) :
    qExpansion h (fun τ : ℍ ↦ 1 - w * 𝕢 h τ ^ c) = 1 - PowerSeries.C w * PowerSeries.X ^ c := by
  have han1 : AnalyticAt ℂ (cuspFunction h (1 : ℍ → ℂ)) 0 := by
    rw [Pi.one_def]
    exact analyticAt_cuspFunction_const h 1
  have hanq := analyticAt_cuspFunction_qParam_pow h c
  have hans := analyticAt_cuspFunction_smul hanq w
  have hfun : (fun τ : ℍ ↦ 1 - w * 𝕢 h τ ^ c) = (1 : ℍ → ℂ) - w • fun τ : ℍ ↦ 𝕢 h τ ^ c :=
    funext fun τ ↦ by simp
  rw [hfun, _root_.UpperHalfPlane.qExpansion_sub han1 hans, _root_.UpperHalfPlane.qExpansion_one,
    _root_.UpperHalfPlane.qExpansion_smul hanq w, qExpansion_qParam_pow hh, Algebra.smul_def,
    PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

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
      funext fun τ ↦ qPochhammerFun_eq_mul hN c w
        (Function.Periodic.norm_qParam_lt_one hh τ.im_pos)
    have hexp (n : ℕ) : N * n + (N + c) = N * (n + 1) + c := by ring
    rw [hfun, _root_.UpperHalfPlane.qExpansion_mul
      (analyticAt_cuspFunction_one_sub_mul_qParam_pow h c w)
      (analyticAt_cuspFunction_qPochhammerFun hh hN _ w),
      qExpansion_one_sub_mul_qParam_pow hh c w, ih (N + c)]
    simp only [hexp, Finset.prod_range_succ', mul_zero, zero_add]
    ring

/-- **The `q`-expansion of a shifted `q`-Pochhammer product.** For `0 < h`, `0 < N`, and `0 < c`,
the `q`-expansion of `τ ↦ ∏_{n ≥ 0} (1 - w 𝕢 h τ^{N n + c})` equals the formal power series
`qPochhammerSeries N c w`. -/
theorem qExpansion_qPochhammerFun (hh : 0 < h) {N c : ℕ} (hN : 0 < N) (hc : 0 < c) (w : ℂ) :
    qExpansion h (fun τ : ℍ ↦ qPochhammerFun N c w (𝕢 h τ)) = qPochhammerSeries N c w := by
  ext m
  set c' := N * m + c
  have hc' : m < c' := by
    have : 1 * m ≤ N * m := Nat.mul_le_mul_right m hN
    omega
  have han1 : AnalyticAt ℂ (cuspFunction h (1 : ℍ → ℂ)) 0 := by
    rw [Pi.one_def]
    exact analyticAt_cuspFunction_const h 1
  have hanP := analyticAt_cuspFunction_qPochhammerFun hh hN c' w
  have hsub_fun : (fun τ : ℍ ↦ qPochhammerFun N c' w (𝕢 h τ) - 1) =
      (fun τ : ℍ ↦ qPochhammerFun N c' w (𝕢 h τ)) - 1 :=
    funext fun τ ↦ by simp
  have han : AnalyticAt ℂ (cuspFunction h fun τ : ℍ ↦ qPochhammerFun N c' w (𝕢 h τ) - 1) 0 := by
    rw [hsub_fun]
    exact analyticAt_cuspFunction_sub hanP han1
  have hzero : ∀ k < c',
      (qExpansion h fun τ : ℍ ↦ qPochhammerFun N c' w (𝕢 h τ) - 1).coeff k = 0 := by
    refine (cuspFunction_isBigO_pow_iff_qExpansion_coeff_eq_zero han).mp ?_
    refine (isBigO_qPochhammerFun_sub_one hN (by omega) w).congr' ?_ EventuallyEq.rfl
    have hsub := _root_.UpperHalfPlane.cuspFunction_sub (h := h) hanP.continuousAt han1.continuousAt
    filter_upwards [cuspFunction_qPochhammerFun_eventuallyEq hh hN c' w] with z hz₁
    rw [hsub_fun, hsub, Pi.sub_apply, cuspFunction_one, Pi.one_apply, hz₁]
  have hsplit : qExpansion h (fun τ : ℍ ↦ qPochhammerFun N c' w (𝕢 h τ)) =
      1 + qExpansion h (fun τ : ℍ ↦ qPochhammerFun N c' w (𝕢 h τ) - 1) := by
    rw [← _root_.UpperHalfPlane.qExpansion_one (h := h),
      ← _root_.UpperHalfPlane.qExpansion_add han1 han]
    exact congrArg (qExpansion h) (funext fun τ ↦ by simp)
  rw [qExpansion_qPochhammerFun_eq_prod_range_mul hh hN c m w, hsplit, mul_add, mul_one, map_add,
    coeff_qPochhammerSeries, PowerSeries.coeff_mul]
  refine add_eq_left.mpr (Finset.sum_eq_zero fun p hp ↦ ?_)
  have hp2 : p.2 ≤ m := by
    have := Finset.mem_antidiagonal.mp hp
    omega
  rw [hzero p.2 (hp2.trans_lt hc'), mul_zero]

end TauCeti.UpperHalfPlane
