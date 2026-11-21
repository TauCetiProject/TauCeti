/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Analysis.SpecialFunctions.Pow.Sector

/-!
# Two-sided complex exponential decay

For a complex rate `a` with positive real part, the function
`x ↦ exp (-(a * |x|))` is little-o of every real power of `|x|` outside compact
subsets of the real line. Its norm is the real exponential with rate `a.re`.

As `z → ∞` in `ℂ`, `e^{-z} = o(1)` in every closed sector `|arg z| ≤ π/2 - δ` with `δ > 0`, but
not in the open right half-plane `|arg z| < π/2` (DLMF §2.1(i), after 2.1.7). These follow the
lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>), file
`DLMF/AsymptoticApproximations/Basics/OrderSymbols.lean`.

## Main results

* `Complex.norm_exp_neg_mul_ofReal`: `‖exp (-(a r))‖ = exp (-(a.re r))` for real `r`.
* `TauCeti.cexp_neg_mul_abs_isLittleO_abs_rpow_cocompact`: two-sided decay with a
  complex rate of positive real part.
* `TauCeti.exp_neg_isLittleO_one_sector`, `TauCeti.not_exp_neg_isLittleO_one_halfPlane`:
  `e^{-z} = o(1)` as `z → ∞` in `|arg z| ≤ π/2 - δ`, and not in `|arg z| < π/2`.
-/

public section

open Filter Asymptotics

/-- For real `r`, the norm of `exp (-(a r))` is the real exponential `exp (-(a.re r))`. -/
theorem Complex.norm_exp_neg_mul_ofReal (a : ℂ) (r : ℝ) :
    ‖Complex.exp (-(a * r))‖ = Real.exp (-(a.re * r)) := by
  simp only [Complex.norm_exp, Complex.neg_re, Complex.re_mul_ofReal]

namespace TauCeti

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
theorem exp_neg_isLittleO_one_sector {δ : ℝ} (hδ : 0 < δ) :
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
  refine (isLittleO_one_iff ℂ).mpr ?_
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h1 : Tendsto (fun z : ℂ => Real.exp (-(c * ‖z‖)))
      (Bornology.cobounded ℂ ⊓ 𝓟 {z | |arg z| ≤ π / 2 - δ}) (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      ((tendsto_norm_cobounded_atTop.mono_left inf_le_left).const_mul_atTop hc)
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h1
  filter_upwards [mem_inf_of_right (mem_principal_self _)] with z hz
  rw [norm_exp, neg_re]
  exact Real.exp_le_exp.mpr (by linarith [hre z hz])

/-- DLMF §2.1(i), after 2.1.7: `e^{-z} = o(1)` fails as `z → ∞` in the open half-plane
`|arg z| < π/2`. Along `z = 1 + it`, `|e^{-z}| = e^{-1}`. -/
theorem not_exp_neg_isLittleO_one_halfPlane :
    ¬ (fun z : ℂ => exp (-z)) =o[Bornology.cobounded ℂ ⊓ 𝓟 {z | |arg z| < π / 2}]
      fun _ => (1 : ℂ) := by
  intro h
  have ht := ((isLittleO_one_iff ℂ).mp h).norm
  set γ : ℝ → ℂ := fun t => 1 + t * I with hγ
  have hγt : Tendsto γ atTop (Bornology.cobounded ℂ ⊓ 𝓟 {z | |arg z| < π / 2}) := by
    refine tendsto_inf.mpr ⟨tendsto_norm_atTop_iff_cobounded.mp ?_, tendsto_principal.mpr
      (Eventually.of_forall fun t => abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by simp [hγ])))⟩
    refine tendsto_atTop_mono (fun t => ?_) tendsto_id
    calc t ≤ |t| := le_abs_self t
      _ = |(γ t).im| := by simp [hγ]
      _ ≤ ‖γ t‖ := abs_im_le_norm _
  have h2 := ht.comp hγt
  have h3 : (fun t => ‖exp (-γ t)‖) = fun _ => Real.exp (-1) := by
    funext t; simp [hγ, norm_exp]
  simp only [Function.comp_def, h3, norm_zero] at h2
  exact (Real.exp_pos (-1)).ne' (tendsto_nhds_unique tendsto_const_nhds h2)

end Sector

end TauCeti
