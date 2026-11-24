/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Analysis.SpecialFunctions.Pow.Sector

/-!
# Two-sided complex exponential decay

For a complex rate `a` with positive real part, the function
`x ↦ exp (-(a * |x|))` is little-o of every real power of `|x|` outside compact
subsets of the real line. Its norm is the real exponential with rate `a.re`. On the closed
left half-plane `Re z ≤ 0` the exponential is `1`-Lipschitz, so `‖1 - exp (-ζ)‖ ≤ ‖ζ‖` for
`0 ≤ ζ.re`.

As `z → ∞` in `ℂ`, `e^{-z} = o(1)` in every closed sector `|arg z| ≤ π/2 - δ` with `δ > 0`, but
not in the open right half-plane `|arg z| < π/2` (DLMF §2.1(i), after 2.1.7). These follow the
lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>), file
`DLMF/AsymptoticApproximations/Basics/OrderSymbols.lean`.

## Main results

* `Complex.norm_exp_neg_mul_ofReal`: `‖exp (-(a r))‖ = exp (-(a.re r))` for real `r`.
* `TauCeti.norm_cexp_neg_mul_lt_one`: `‖exp (-(h : ℂ) * z)‖ < 1` for `h > 0` and `0 < z.re`.
* `TauCeti.cexp_neg_mul_abs_isLittleO_abs_rpow_cocompact`: two-sided decay with a
  complex rate of positive real part.
* `Complex.lipschitzOnWith_exp_setOf_re_nonpos`: `exp` is `1`-Lipschitz on `Re z ≤ 0`.
* `Complex.norm_one_sub_exp_neg_le`: `‖1 - exp (-ζ)‖ ≤ ‖ζ‖` for `0 ≤ ζ.re`.
* `TauCeti.cexp_neg_isLittleO_one_sector`, `TauCeti.not_cexp_neg_isLittleO_one_rightHalfPlane`:
  `e^{-z} = o(1)` as `z → ∞` in `|arg z| ≤ π/2 - δ` with `δ > 0`, and not in `|arg z| < π/2`.
-/

public section

open Filter Asymptotics

/-- For real `r`, the norm of `exp (-(a r))` is the real exponential `exp (-(a.re r))`. -/
theorem Complex.norm_exp_neg_mul_ofReal (a : ℂ) (r : ℝ) :
    ‖Complex.exp (-(a * r))‖ = Real.exp (-(a.re * r)) := by
  simp only [Complex.norm_exp, Complex.neg_re, Complex.re_mul_ofReal]

/-- On the closed left half-plane `Re z ≤ 0` the exponential is `1`-Lipschitz: its derivative
`exp z` has norm `exp (Re z) ≤ 1` there. -/
theorem Complex.lipschitzOnWith_exp_setOf_re_nonpos :
    LipschitzOnWith 1 Complex.exp {z : ℂ | z.re ≤ 0} :=
  (convex_halfSpace_re_le 0).lipschitzOnWith_of_nnNorm_hasDerivWithin_le
    (fun z _ => (Complex.hasDerivAt_exp z).hasDerivWithinAt) fun z hz => by
      simpa only [← NNReal.coe_le_coe, coe_nnNorm, NNReal.coe_one, Complex.norm_exp,
        Real.exp_le_one_iff, Set.mem_ofPred_eq] using hz

/-- On the closed right half-plane, `‖1 - exp (-ζ)‖ ≤ ‖ζ‖`: the case `0`, `-ζ` of
`Complex.lipschitzOnWith_exp_setOf_re_nonpos`. -/
theorem Complex.norm_one_sub_exp_neg_le {ζ : ℂ} (hζ : 0 ≤ ζ.re) :
    ‖1 - Complex.exp (-ζ)‖ ≤ ‖ζ‖ := by
  have h := Complex.lipschitzOnWith_exp_setOf_re_nonpos.norm_sub_le
    (x := 0) (y := -ζ) (by simp) (by simpa using hζ)
  simpa using h

namespace TauCeti

/-- For `h > 0` and `0 < z.re`, the complex exponential `exp (-(h : ℂ) * z)` has norm strictly less
than `1`. -/
theorem norm_cexp_neg_mul_lt_one {h : ℝ} (hh : 0 < h) {z : ℂ} (hz : 0 < z.re) :
    ‖Complex.exp (-(h : ℂ) * z)‖ < 1 := by
  rw [neg_mul, mul_comm (h : ℂ) z, Complex.norm_exp_neg_mul_ofReal]
  exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (mul_pos hz hh))

/-- **Two-sided complex exponential decay beats every real power.** If a complex rate
has positive real part, then `exp (-(a * |x|))` is little-o of `|x| ^ s` as
`|x|` tends to infinity, for every real `s`.

The real-valued estimate is `exp_neg_mul_abs_isLittleO_abs_rpow_cocompact`.

Adapted from `ForTauCeti/Analysis/Fourier/ExponentialAbs.lean` in
[AIQ-Kitware/aiq-dkps-formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization)
(Apache-2.0; copyright 2026 Kitware, Inc.; authors Jon Crall and GPT 5.6 High). -/
theorem cexp_neg_mul_abs_isLittleO_abs_rpow_cocompact
    {a : ℂ} (ha : 0 < a.re) (s : ℝ) :
    (fun x : ℝ => Complex.exp (-(a * |x|)))
      =o[cocompact ℝ] (fun x : ℝ => |x| ^ s) := by
  apply IsLittleO.of_norm_left
  simpa only [Complex.norm_exp_neg_mul_ofReal] using
    (exp_neg_mul_abs_isLittleO_abs_rpow_cocompact ha s)

section Sector

open Complex
open scoped Topology Real

/-- DLMF §2.1(i), after 2.1.7: `e^{-z} = o(1)` as `z → ∞` in the closed sector
`|arg z| ≤ π/2 - δ`, for every `δ > 0`. -/
theorem cexp_neg_isLittleO_one_sector {δ : ℝ} (hδ : 0 < δ) :
    (fun z : ℂ => exp (-z)) =o[Bornology.cobounded ℂ ⊓ 𝓟 {z | |arg z| ≤ π / 2 - δ}]
      fun _ => (1 : ℂ) := by
  rcases lt_or_ge (π / 2 - δ) 0 with hneg | hnn
  · have hempty : {z : ℂ | |arg z| ≤ π / 2 - δ} = ∅ :=
      Set.eq_empty_of_forall_notMem fun z hz => (abs_nonneg _).not_gt (hz.trans_lt hneg)
    simp [hempty]
  set c := Real.sin δ
  have hc : 0 < c := Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_pos])
  have hre : ∀ z : ℂ, |arg z| ≤ π / 2 - δ → c * ‖z‖ ≤ z.re := fun z hz => by
    have h := (TauCeti.arg_mem_Icc_iff_norm_mul_cos_le_re (z := z)
      ⟨hnn, by linarith [Real.pi_pos]⟩).mp (abs_le.mp hz)
    rwa [Real.cos_pi_div_two_sub, mul_comm] at h
  refine (isLittleO_one_iff ℂ).mpr (tendsto_exp_nhds_zero_iff.mpr ?_)
  simp only [neg_re]
  refine tendsto_neg_atTop_atBot.comp (tendsto_atTop_mono' _ ?_
    ((tendsto_norm_cobounded_atTop.mono_left inf_le_left).const_mul_atTop hc))
  filter_upwards [mem_inf_of_right (mem_principal_self _)] with z hz
  exact hre z hz

/-- DLMF §2.1(i), after 2.1.7: `e^{-z} = o(1)` fails as `z → ∞` in the open half-plane
`|arg z| < π/2`. Along `z = 1 + it`, `|e^{-z}| = e^{-1}`. -/
theorem not_cexp_neg_isLittleO_one_rightHalfPlane :
    ¬ (fun z : ℂ => exp (-z)) =o[Bornology.cobounded ℂ ⊓ 𝓟 {z | |arg z| < π / 2}]
      fun _ => (1 : ℂ) := by
  intro h
  have ht := tendsto_exp_nhds_zero_iff.mp ((isLittleO_one_iff ℂ).mp h)
  set γ : ℝ → ℂ := fun t => 1 + t * I with hγ
  have hγt : Tendsto γ atTop (Bornology.cobounded ℂ ⊓ 𝓟 {z | |arg z| < π / 2}) := by
    refine tendsto_inf.mpr ⟨tendsto_norm_atTop_iff_cobounded.mp ?_, tendsto_principal.mpr
      (Eventually.of_forall fun t => abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by simp [hγ])))⟩
    refine tendsto_atTop_mono (fun t => ?_) tendsto_id
    calc t ≤ |t| := le_abs_self t
      _ = |(γ t).im| := by simp [hγ]
      _ ≤ ‖γ t‖ := abs_im_le_norm _
  -- Along `γ` the real part of `-z` is constantly `-1`, which does not tend to `-∞`.
  have h2 := ht.comp hγt
  simp only [Function.comp_def, hγ, neg_re, add_re, one_re, mul_re, ofReal_re, I_re, mul_zero,
    ofReal_im, I_im, mul_one, sub_self, add_zero] at h2
  exact not_tendsto_const_atBot (-1 : ℝ) atTop h2

end Sector

end TauCeti
