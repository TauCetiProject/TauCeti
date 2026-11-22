/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.MellinTransform.CompactSupport
public import TauCeti.Analysis.MellinTransform.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Delta spikes and smoothed cutoffs for Mellin transforms

This file develops multiplicative smoothing on `(0, ∞)` using rescaled bump functions (delta
spikes) and smoothed step functions (smoothed cutoffs).

For a bump `ν : ℝ → ℝ` and scale `ε > 0`, the delta spike
`deltaSpike ν ε x = ε⁻¹ * ν (x ^ ε⁻¹)` (for `x > 0`, and `0` for `x ≤ 0`) rescales support in
`[a, b] ⊂ (0, ∞)` to `[a ^ ε, b ^ ε]`, preserves the multiplicative Haar mass `∫₀^∞ ν(x) dx / x`,
and satisfies `mellin (deltaSpike ν ε) s = mellin ν (ε * s)`. When `ν ≥ 0` is supported in
`[a, b] ⊂ (0, ∞)` with `∫₀^∞ ν(x) dx / x = 1`, convolution with `deltaSpike ν ε` forms an
approximate identity for `dx / x` (pointwise at continuity points and uniformly on compact subsets
of `(0, ∞)`), and `‖mellin ν ε - 1‖ ≤ max b 1 * max |log a| |log b| * ε` for `0 ≤ ε ≤ 1`.

The smoothed cutoff `smoothCutoff ν ε x = ∫_{(x, ∞)} deltaSpike ν ε z dz / z` (for `x > 0`, and
`0` for `x ≤ 0`) equals the Mellin convolution of `(Ioc 0 1).indicator 1` with `deltaSpike ν ε`
on `(0, ∞)`. For a nonnegative bump supported in `[a, b] ⊂ (0, ∞)` with `dx / x`-mass `1`, it
satisfies `0 ≤ smoothCutoff ν ε ≤ 1`, equals `1` on `(0, a ^ ε]` and `0` on `[b ^ ε, ∞)` (and
`1 / 2` at `x = 1` when `ν (x⁻¹) = ν x`), is continuous on `(0, ∞)`, and has Mellin transform
`mellin ν (ε * s) / s` for `Re s > 0`. When `ν` is `C^k` on `(0, ∞)`, this gives the uniform-in-`ε`
decay bound `‖mellin (smoothCutoff ν ε) s‖ ≤ C / (‖s‖ * (1 + ε * ‖s‖) ^ k)` on vertical strips
`0 < σ₁ ≤ Re s ≤ σ₂`, and vertical integrability whenever `k ≥ 1`.

## Main definitions

* `TauCeti.deltaSpike`: the multiplicatively rescaled bump `ε⁻¹ * ν (x ^ ε⁻¹)` on `(0, ∞)`.
* `TauCeti.smoothCutoff`: the tail integral `∫_{(x, ∞)} deltaSpike ν ε z dz / z` on `(0, ∞)`.

## Main results

* `TauCeti.mellin_deltaSpike`, `TauCeti.integral_deltaSpike_div`: Mellin transform and Haar mass
  of `deltaSpike`.
* `TauCeti.norm_mellinConv_deltaSpike_sub_le`, `TauCeti.tendsto_mellinConv_deltaSpike`,
  `TauCeti.tendstoUniformlyOn_mellinConv_deltaSpike`: the approximate identity for `dx / x`.
* `TauCeti.smoothCutoff_eq_mellinConv`: `smoothCutoff` as a Mellin convolution on `(0, ∞)`.
* `TauCeti.hasMellin_smoothCutoff`, `TauCeti.mellin_smoothCutoff`: Mellin transform of
  `smoothCutoff`.
* `TauCeti.norm_mellin_smoothCutoff_le`: uniform-in-`ε` vertical-strip decay of
  `mellin (smoothCutoff ν ε)`.
* `TauCeti.verticalIntegrable_mellin_smoothCutoff`: vertical integrability for `C^k` bumps
  (`k ≥ 1`).
* `TauCeti.exists_smooth_symmetric_bump`: existence of a symmetric `C^∞` bump supported in
  `[R⁻¹, R]` (`1 < R`) with `dx / x`-mass `1`.

## References

* A. Kontorovich, T. Tao and contributors, *Prime Number Theorem And …*, §4.3 (delta spikes and
  smoothed cutoffs).
-/

public section

open MeasureTheory Complex Set Filter
open scoped Topology ContDiff

namespace TauCeti

/-! ### Delta spikes -/

/-- The delta spike associated to a bump `ν : ℝ → ℝ` and scale `ε : ℝ`:
`deltaSpike ν ε x = ε⁻¹ * ν (x ^ ε⁻¹)` for `x > 0` and `0` for `x ≤ 0`. -/
noncomputable def deltaSpike (ν : ℝ → ℝ) (ε x : ℝ) : ℝ :=
  if 0 < x then ε⁻¹ * ν (x ^ ε⁻¹) else 0

/-- Definitional unfolding of `deltaSpike`. -/
theorem deltaSpike_def (ν : ℝ → ℝ) (ε x : ℝ) :
    deltaSpike ν ε x = if 0 < x then ε⁻¹ * ν (x ^ ε⁻¹) else 0 := (rfl)

@[simp]
theorem deltaSpike_of_pos {ν : ℝ → ℝ} {ε x : ℝ} (hx : 0 < x) :
    deltaSpike ν ε x = ε⁻¹ * ν (x ^ ε⁻¹) := by
  simp [deltaSpike_def, hx]

@[simp]
theorem deltaSpike_of_nonpos {ν : ℝ → ℝ} {ε x : ℝ} (hx : x ≤ 0) :
    deltaSpike ν ε x = 0 := by
  simp [deltaSpike_def, hx.not_gt]

/-- `deltaSpike` vanishes at `0`. -/
theorem deltaSpike_zero (ν : ℝ → ℝ) (ε : ℝ) : deltaSpike ν ε 0 = 0 :=
  deltaSpike_of_nonpos le_rfl

/-- At `ε = 1`, `deltaSpike ν 1` agrees with `ν` on `(0, ∞)`. -/
theorem deltaSpike_one_of_pos (ν : ℝ → ℝ) {x : ℝ} (hx : 0 < x) :
    deltaSpike ν 1 x = ν x := by
  simp [hx]

/-- Nonnegativity of `deltaSpike` for nonnegative `ν` and `ε ≥ 0`. -/
theorem deltaSpike_nonneg {ν : ℝ → ℝ} (hν : ∀ x, 0 ≤ ν x) {ε : ℝ} (hε : 0 ≤ ε) (x : ℝ) :
    0 ≤ deltaSpike ν ε x := by
  rw [deltaSpike_def]
  split_ifs
  · exact mul_nonneg (inv_nonneg.mpr hε) (hν _)
  · exact le_rfl

/-- Multiplicative inversion symmetry of `deltaSpike` when `ν (x⁻¹) = ν x` on `(0, ∞)`. -/
theorem deltaSpike_inv_of_symm {ν : ℝ → ℝ} (hsym : ∀ x, 0 < x → ν x⁻¹ = ν x) (ε : ℝ)
    {x : ℝ} (hx : 0 < x) :
    deltaSpike ν ε x⁻¹ = deltaSpike ν ε x := by
  rw [deltaSpike_of_pos (inv_pos.mpr hx), deltaSpike_of_pos hx, Real.inv_rpow hx.le,
    hsym _ (Real.rpow_pos_of_pos hx _)]

/-- If `ν` is supported in `[a, b]` with `0 < a` and `ε > 0`, then `deltaSpike ν ε` is supported
in `[a ^ ε, b ^ ε]`. -/
theorem support_deltaSpike_subset_Icc {ν : ℝ → ℝ} {a b ε : ℝ} (ha : 0 < a) (hε : 0 < ε)
    (hsupp : Function.support ν ⊆ Icc a b) :
    Function.support (deltaSpike ν ε) ⊆ Icc (a ^ ε) (b ^ ε) := by
  intro x hx
  have hx0 : 0 < x := by
    by_contra h
    exact hx (deltaSpike_of_nonpos (le_of_not_gt h))
  rw [Function.mem_support, deltaSpike_of_pos hx0] at hx
  have hνx : x ^ ε⁻¹ ∈ Icc a b := hsupp (right_ne_zero_of_mul hx)
  have hpow : (x ^ ε⁻¹) ^ ε = x := by
    rw [← Real.rpow_mul hx0.le, inv_mul_cancel₀ hε.ne', Real.rpow_one]
  refine ⟨?_, ?_⟩
  · rw [← hpow]
    exact Real.rpow_le_rpow ha.le hνx.1 hε.le
  · rw [← hpow]
    exact Real.rpow_le_rpow (ha.le.trans hνx.1) hνx.2 hε.le

/-- Mellin convergence of `deltaSpike ν ε` at `s` is equivalent to Mellin convergence of `ν` at
`ε * s` for every `ε > 0`. -/
theorem mellinConvergent_deltaSpike_iff {ν : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε) (s : ℂ) :
    MellinConvergent (fun x ↦ (deltaSpike ν ε x : ℂ)) s ↔
      MellinConvergent (fun x ↦ (ν x : ℂ)) (ε * s) := by
  have hcongr : MellinConvergent (fun x ↦ (deltaSpike ν ε x : ℂ)) s ↔
      MellinConvergent (fun x ↦ (ε⁻¹ : ℂ) * (ν (x ^ ε⁻¹) : ℂ)) s := by
    refine integrableOn_congr_fun (fun x hx ↦ ?_) measurableSet_Ioi
    simp only [deltaSpike_of_pos hx, ofReal_mul, ofReal_inv]
  have hsmul : MellinConvergent (fun x ↦ (ε⁻¹ : ℂ) * (ν (x ^ ε⁻¹) : ℂ)) s ↔
      MellinConvergent (fun x ↦ (ν (x ^ ε⁻¹) : ℂ)) s := by
    have hεc : (ε⁻¹ : ℂ) ≠ 0 := inv_ne_zero (ofReal_ne_zero.mpr hε.ne')
    have hEq : (fun x : ℝ ↦ (x : ℂ) ^ (s - 1) • ((ε⁻¹ : ℂ) * (ν (x ^ ε⁻¹) : ℂ))) =
        (ε⁻¹ : ℂ) • fun x : ℝ ↦ (x : ℂ) ^ (s - 1) • (ν (x ^ ε⁻¹) : ℂ) := by
      ext x
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [MellinConvergent, MellinConvergent, hEq, IntegrableOn, IntegrableOn,
      integrable_smul_iff hεc]
  rw [hcongr, hsmul, MellinConvergent.comp_rpow (f := fun x ↦ (ν x : ℂ)) (inv_ne_zero hε.ne'),
    ofReal_inv, div_inv_eq_mul, mul_comm]

/-- The Mellin transform of `deltaSpike ν ε` at `s` equals `mellin ν (ε * s)` for every `ε > 0`,
with no convergence or support hypothesis on `ν`. -/
theorem mellin_deltaSpike (ν : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) (s : ℂ) :
    mellin (fun x ↦ (deltaSpike ν ε x : ℂ)) s = mellin (fun x ↦ (ν x : ℂ)) (ε * s) := by
  have hcongr : mellin (fun x ↦ (deltaSpike ν ε x : ℂ)) s =
      mellin (fun x ↦ ε⁻¹ • (ν (x ^ ε⁻¹) : ℂ)) s := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
    simp only [deltaSpike_of_pos hx, ofReal_mul, ofReal_inv, Complex.real_smul]
  rw [hcongr, mellin_const_smul, mellin_comp_rpow (fun x ↦ (ν x : ℂ)) s ε⁻¹,
    abs_of_pos (inv_pos.mpr hε), inv_inv, smul_smul, inv_mul_cancel₀ hε.ne', one_smul,
    ofReal_inv, div_inv_eq_mul, mul_comm]

/-- Rescaling `ν` to `deltaSpike ν ε` preserves the multiplicative Haar integral
`∫₀^∞ ν(x) dx / x` for every `ε > 0`, with no integrability hypothesis. -/
theorem integral_deltaSpike_div (ν : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    (∫ x in Ioi (0 : ℝ), deltaSpike ν ε x / x) = ∫ x in Ioi (0 : ℝ), ν x / x := by
  apply Complex.ofReal_injective
  rw [← mellin_ofReal_zero, ← mellin_ofReal_zero, mellin_deltaSpike ν hε 0, mul_zero]

/-- Integrability of `deltaSpike ν ε x / x` on `(0, ∞)` is equivalent to integrability of
`ν x / x` on `(0, ∞)` for every `ε > 0`. -/
theorem integrableOn_deltaSpike_div_iff {ν : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun x ↦ deltaSpike ν ε x / x) (Ioi (0 : ℝ)) ↔
      IntegrableOn (fun x ↦ ν x / x) (Ioi (0 : ℝ)) := by
  rw [← mellinConvergent_ofReal_zero_iff, ← mellinConvergent_ofReal_zero_iff,
    mellinConvergent_deltaSpike_iff hε 0, mul_zero]

private lemma mellin_ofReal_sub_one_eq {ν : ℝ → ℝ} {a b ε : ℝ} (ha : 0 < a)
    (hνs : Function.support ν ⊆ Icc a b) (hνm : ∫ x in Ioi (0 : ℝ), ν x / x = 1) :
    mellin (fun x ↦ (ν x : ℂ)) (ε : ℂ) - 1 =
      ((∫ x in Ioi (0 : ℝ), (x ^ ε - 1) * (ν x / x) : ℝ) : ℂ) ∧
      IntegrableOn (fun x ↦ (x ^ ε - 1) * (ν x / x)) (Ioi (0 : ℝ)) := by
  have hconv_0 : MellinConvergent (fun x ↦ (ν x : ℂ)) 0 :=
    (mellinConvergent_ofReal_zero_iff ν).mpr (integrable_of_integral_eq_one hνm)
  have hconv_ε : MellinConvergent (fun x ↦ (ν x : ℂ)) (ε : ℂ) :=
    hconv_0.of_support_subset_Icc ha (fun x hx ↦ hνs fun h ↦ hx (by simp [h])) (ε : ℂ)
  have hpt : EqOn (fun x : ℝ ↦ (x : ℂ) ^ ((ε : ℂ) - 1) • (ν x : ℂ) -
      (x : ℂ) ^ ((0 : ℂ) - 1) • (ν x : ℂ))
      (fun x : ℝ ↦ ((((x ^ ε - 1) * (ν x / x) : ℝ) : ℂ))) (Ioi (0 : ℝ)) := fun x hx ↦ by
    have hxc : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hx)
    simp only [smul_eq_mul, zero_sub, cpow_neg_one]
    rw [cpow_sub _ _ hxc, cpow_one, ← ofReal_cpow hx.le]
    push_cast
    field_simp [hxc]
  refine ⟨?_, Complex.reCLM.integrable_comp ((hconv_ε.sub hconv_0).congr_fun hpt measurableSet_Ioi)⟩
  have h1 : (1 : ℂ) = mellin (fun x ↦ (ν x : ℂ)) 0 := by rw [mellin_ofReal_zero, hνm, ofReal_one]
  rw [h1, mellin, mellin, ← integral_sub hconv_ε hconv_0,
    setIntegral_congr_fun measurableSet_Ioi hpt, integral_complex_ofReal]

/-- For a nonnegative bump `ν` supported in `[a, b] ⊂ (0, ∞)` with `∫₀^∞ ν(x) dx / x = 1` and
`0 ≤ ε ≤ 1`, `‖mellin ν ε - 1‖ ≤ max b 1 * max |log a| |log b| * ε`. -/
theorem norm_mellin_ofReal_sub_one_le {ν : ℝ → ℝ} {a b ε : ℝ} (ha : 0 < a)
    (hν0 : ∀ x, 0 ≤ ν x) (hνs : Function.support ν ⊆ Icc a b)
    (hνm : ∫ x in Ioi (0 : ℝ), ν x / x = 1) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ‖mellin (fun x ↦ (ν x : ℂ)) (ε : ℂ) - 1‖ ≤
      max b 1 * max |Real.log a| |Real.log b| * ε := by
  have hint_div : IntegrableOn (fun x ↦ ν x / x) (Ioi (0 : ℝ)) := integrable_of_integral_eq_one hνm
  obtain ⟨hsub, hint_real⟩ := mellin_ofReal_sub_one_eq (ε := ε) ha hνs hνm
  rw [hsub, Complex.norm_real, Real.norm_eq_abs]
  set L := max |Real.log a| |Real.log b|
  have hpow_bd {x : ℝ} (hx : x ∈ Icc a b) : |x ^ ε - 1| ≤ max b 1 * L * ε := by
    have hx0 : 0 < x := ha.trans_le hx.1
    have hlog_abs : |Real.log x| ≤ L := abs_le.mpr
      ⟨(neg_le_neg (le_max_left _ _)).trans ((neg_abs_le _).trans (Real.log_le_log ha hx.1)),
        (Real.log_le_log hx0 hx.2).trans ((le_abs_self _).trans (le_max_right _ _))⟩
    rw [Real.rpow_def_of_pos hx0, mul_comm (Real.log x) ε]
    set u := ε * Real.log x
    rcases le_or_gt 0 (Real.log x) with hlog_nn | hlog_neg
    · have hu_le : u ≤ ε * L := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hlog_abs) hε0
      have hexp_le : Real.exp u ≤ max b 1 :=
        ((Real.exp_le_exp.mpr ((mul_le_of_le_one_left hlog_nn hε1).trans
          (Real.log_le_log hx0 hx.2))).trans_eq (Real.exp_log (hx0.trans_le hx.2))).trans
          (le_max_left b 1)
      have h1 : Real.exp u - 1 ≤ u * Real.exp u := by
        have hmul := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-u)) (Real.exp_pos u).le
        rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at hmul
        linarith
      rw [abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp (mul_nonneg hε0 hlog_nn)))]
      calc Real.exp u - 1 ≤ u * Real.exp u := h1
        _ ≤ (ε * L) * max b 1 := mul_le_mul hu_le hexp_le (Real.exp_pos u).le (by positivity)
        _ = max b 1 * L * ε := by ring
    · have hnegu : -u ≤ ε * L := by
        simpa [u, mul_neg] using mul_le_mul_of_nonneg_left ((neg_le_abs _).trans hlog_abs) hε0
      rw [abs_of_nonpos (sub_nonpos.mpr
        (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hε0 hlog_neg.le))), neg_sub]
      nlinarith [Real.add_one_le_exp u, le_max_right b 1,
        mul_nonneg hε0 (le_trans (abs_nonneg _) (le_max_left |Real.log a| |Real.log b|))]
  calc |∫ x in Ioi (0 : ℝ), (x ^ ε - 1) * (ν x / x)|
    _ ≤ ∫ x in Ioi (0 : ℝ), |(x ^ ε - 1) * (ν x / x)| := abs_integral_le_integral_abs
    _ ≤ ∫ x in Ioi (0 : ℝ), (max b 1 * L * ε) * (ν x / x) := by
        refine setIntegral_mono_on hint_real.abs (hint_div.const_mul _) measurableSet_Ioi
          fun x hx ↦ ?_
        rw [abs_mul, abs_of_nonneg (div_nonneg (hν0 x) hx.le)]
        by_cases hνx : ν x = 0
        · simp [hνx]
        · exact mul_le_mul_of_nonneg_right (hpow_bd (hνs hνx)) (div_nonneg (hν0 x) hx.le)
    _ = max b 1 * L * ε := by rw [integral_const_mul, hνm, mul_one]

/-- For a nonnegative bump `ν` supported in `[a, b] ⊂ (0, ∞)` with `∫₀^∞ ν(x) dx / x = 1` and
`0 < ε ≤ 1`, `‖mellin (deltaSpike ν ε) 1 - 1‖ ≤ max b 1 * max |log a| |log b| * ε`. -/
theorem norm_mellin_deltaSpike_one_sub_one_le {ν : ℝ → ℝ} {a b ε : ℝ} (ha : 0 < a)
    (hν0 : ∀ x, 0 ≤ ν x) (hνs : Function.support ν ⊆ Icc a b)
    (hνm : ∫ x in Ioi (0 : ℝ), ν x / x = 1) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ‖mellin (fun x ↦ (deltaSpike ν ε x : ℂ)) 1 - 1‖ ≤
      max b 1 * max |Real.log a| |Real.log b| * ε := by
  rw [mellin_deltaSpike ν hε0 1, mul_one]
  exact norm_mellin_ofReal_sub_one_le ha hν0 hνs hνm hε0.le hε1

/-! ### Approximate identity for `dx / x` -/

/-- Integrability of the difference integrand `(deltaSpike ν ε y / y) * (f (x / y) - f x)` on
`(0, ∞)` when `‖f (x / y) - f x‖ ≤ M` on the support `[a ^ ε, b ^ ε]` of `deltaSpike ν ε`. -/
private lemma integrableOn_deltaSpike_div_mul_sub {ν : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hν0 : ∀ x, 0 ≤ ν x) (hνs : Function.support ν ⊆ Icc a b)
    (hνm : ∫ x in Ioi (0 : ℝ), ν x / x = 1)
    {f : ℝ → ℂ} (hf : AEStronglyMeasurable f (volume.restrict (Ioi (0 : ℝ))))
    {ε x M : ℝ} (hε : 0 < ε) (hx : 0 < x)
    (hbd : ∀ y ∈ Icc (a ^ ε) (b ^ ε), ‖f (x / y) - f x‖ ≤ M) :
    IntegrableOn (fun y : ℝ ↦ ((deltaSpike ν ε y / y : ℝ) : ℂ) * (f (x / y) - f x))
      (Ioi (0 : ℝ)) := by
  obtain ⟨x₀, hx₀⟩ := exists_ne_zero_of_integral_ne_zero (hνm ▸ one_ne_zero)
  have hx₀' : x₀ ∈ Icc a b := hνs (left_ne_zero_of_mul (div_eq_mul_inv (ν x₀) x₀ ▸ hx₀))
  have hb : 0 < b := ha.trans_le (hx₀'.1.trans hx₀'.2)
  have hint_spike : IntegrableOn (fun y ↦ deltaSpike ν ε y / y) (Ioi (0 : ℝ)) :=
    (integrableOn_deltaSpike_div_iff hε).mpr (integrable_of_integral_eq_one hνm)
  have hsupp_spike := support_deltaSpike_subset_Icc ha hε hνs
  set c := x / b ^ ε
  set d := x / a ^ ε
  have hc : 0 < c := div_pos hx (Real.rpow_pos_of_pos hb ε)
  have hIcc_sub : Icc c d ⊆ Ioi (0 : ℝ) := fun _ hz ↦ hc.trans_le hz.1
  -- Restrict `f` to `[x / b ^ ε, x / a ^ ε]` where it is bounded, then pull back via `y ↦ x * y⁻¹`.
  have hint_ind : IntegrableOn ((Icc c d).indicator f) (Ioi (0 : ℝ)) := by
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Icc, IntegrableOn,
      Measure.restrict_restrict_of_subset hIcc_sub]
    refine (integrableOn_const (hs := isCompact_Icc.measure_lt_top.ne)
      (C := max (‖f x‖ + M) 0)).mono' (hf.mono_set hIcc_sub)
      ((ae_restrict_mem measurableSet_Icc).mono fun z hz ↦ ?_)
    have hz0 : 0 < z := hc.trans_le hz.1
    have hxz : x / z ∈ Icc (a ^ ε) (b ^ ε) :=
      ⟨(le_div_iff₀ hz0).mpr (by linarith [(le_div_iff₀ (Real.rpow_pos_of_pos ha ε)).mp hz.2]),
        (div_le_iff₀ hz0).mpr (by linarith [(div_le_iff₀ (Real.rpow_pos_of_pos hb ε)).mp hz.1])⟩
    have hdiff := hbd (x / z) hxz
    have hdiv : x / (x / z) = z := by field_simp [hx.ne', hz0.ne']
    rw [hdiv] at hdiff
    have htri : ‖f z‖ ≤ ‖f z - f x‖ + ‖f x‖ := by simpa using norm_add_le (f z - f x) (f x)
    exact (by linarith : ‖f z‖ ≤ ‖f x‖ + M).trans (le_max_left _ 0)
  have hcomp_int : IntegrableOn (fun y : ℝ ↦ (y ^ (-1 - 1 : ℝ)) •
      (Icc c d).indicator f (x * y ^ (-1 : ℝ))) (Ioi (0 : ℝ)) :=
    (integrableOn_Ioi_comp_rpow_iff' (fun y : ℝ ↦ (Icc c d).indicator f (x * y))
      (by norm_num : (-1 : ℝ) ≠ 0)).mpr
      ((integrableOn_Ioi_comp_mul_left_iff ((Icc c d).indicator f) 0 hx).mpr
        (by simpa [mul_zero] using hint_ind))
  have hmeas_ind : AEStronglyMeasurable (fun y : ℝ ↦ (Icc c d).indicator f (x / y))
      (volume.restrict (Ioi (0 : ℝ))) := by
    have hmeas_sq : AEStronglyMeasurable (fun y : ℝ ↦ y ^ (2 : ℝ))
        (volume.restrict (Ioi (0 : ℝ))) :=
      (continuousOn_of_forall_continuousAt fun y hy ↦
        Real.continuousAt_rpow_const y 2 (Or.inl (ne_of_gt hy))).aestronglyMeasurable
        measurableSet_Ioi
    refine (hmeas_sq.smul hcomp_int.aestronglyMeasurable).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    rw [Pi.smul_apply', smul_smul, ← Real.rpow_add hy, (by norm_num : (2 : ℝ) + (-1 - 1) = 0),
      Real.rpow_zero, one_smul, Real.rpow_neg_one, ← div_eq_mul_inv]
  -- On the support of `deltaSpike ν ε`, the cutoff indicator agrees with `f (x / y)`.
  have hmeas_diff : AEStronglyMeasurable
      (fun y : ℝ ↦ ((deltaSpike ν ε y / y : ℝ) : ℂ) * (f (x / y) - f x))
      (volume.restrict (Ioi (0 : ℝ))) := by
    refine ((Complex.ofRealCLM.integrable_comp hint_spike).aestronglyMeasurable.mul
      (hmeas_ind.sub (aestronglyMeasurable_const (b := f x)))).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    by_cases hdy : deltaSpike ν ε y = 0
    · simp [hdy]
    · have hxy : x / y ∈ Icc c d :=
        ⟨div_le_div_of_nonneg_left hx.le hy (hsupp_spike hdy).2,
          div_le_div_of_nonneg_left hx.le (Real.rpow_pos_of_pos ha ε) (hsupp_spike hdy).1⟩
      simp only [Pi.mul_apply, Pi.sub_apply, ofRealCLM_apply, indicator_of_mem hxy]
  refine (hint_spike.const_mul M).mono' hmeas_diff ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (deltaSpike_nonneg hν0 hε.le y) hy.le)]
  by_cases hdy : deltaSpike ν ε y = 0
  · simp [hdy]
  · rw [mul_comm M]
    exact mul_le_mul_of_nonneg_left (hbd y (hsupp_spike hdy))
      (div_nonneg (deltaSpike_nonneg hν0 hε.le y) hy.le)

/-- Quantitative approximate-identity bound: if `ν ≥ 0` is supported in `[a, b] ⊂ (0, ∞)` with
`∫₀^∞ ν(x) dx / x = 1` and `‖f (x / y) - f x‖ ≤ M` for all `y ∈ [a ^ ε, b ^ ε]`, then
`‖mellinConv (deltaSpike ν ε) f x - f x‖ ≤ M`. -/
theorem norm_mellinConv_deltaSpike_sub_le {ν : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hν0 : ∀ x, 0 ≤ ν x) (hνs : Function.support ν ⊆ Icc a b)
    (hνm : ∫ x in Ioi (0 : ℝ), ν x / x = 1)
    {f : ℝ → ℂ} (hf : AEStronglyMeasurable f (volume.restrict (Ioi (0 : ℝ))))
    {ε x M : ℝ} (hε : 0 < ε) (hx : 0 < x)
    (hbd : ∀ y ∈ Icc (a ^ ε) (b ^ ε), ‖f (x / y) - f x‖ ≤ M) :
    ‖mellinConv (fun y ↦ (deltaSpike ν ε y : ℂ)) f x - f x‖ ≤ M := by
  have hint_spike : IntegrableOn (fun y ↦ deltaSpike ν ε y / y) (Ioi (0 : ℝ)) :=
    (integrableOn_deltaSpike_div_iff hε).mpr (integrable_of_integral_eq_one hνm)
  have hmass : ∫ y in Ioi (0 : ℝ), deltaSpike ν ε y / y = 1 := by
    rw [integral_deltaSpike_div ν hε, hνm]
  have hsupp_spike := support_deltaSpike_subset_Icc ha hε hνs
  have hint_diff := integrableOn_deltaSpike_div_mul_sub ha hν0 hνs hνm hf hε hx hbd
  have hint_const : IntegrableOn
      (fun y : ℝ ↦ ((deltaSpike ν ε y / y : ℝ) : ℂ) * f x) (Ioi (0 : ℝ)) :=
    (Complex.ofRealCLM.integrable_comp hint_spike).mul_const (f x)
  have hsub_eq : mellinConv (fun y ↦ (deltaSpike ν ε y : ℂ)) f x - f x =
      ∫ y in Ioi (0 : ℝ), ((deltaSpike ν ε y / y : ℝ) : ℂ) * (f (x / y) - f x) := by
    have hfx_eq : f x = ∫ y in Ioi (0 : ℝ), ((deltaSpike ν ε y / y : ℝ) : ℂ) * f x := by
      rw [integral_mul_const, integral_complex_ofReal, hmass, ofReal_one, one_mul]
    have hconv_eq : mellinConv (fun y ↦ (deltaSpike ν ε y : ℂ)) f x =
        ∫ y in Ioi (0 : ℝ),
          (((deltaSpike ν ε y / y : ℝ) : ℂ) * (f (x / y) - f x) +
            ((deltaSpike ν ε y / y : ℝ) : ℂ) * f x) := by
      rw [mellinConv_def]
      refine setIntegral_congr_fun measurableSet_Ioi fun y _ ↦ ?_
      push_cast
      ring
    rw [hconv_eq, integral_add hint_diff hint_const, ← hfx_eq, add_sub_cancel_right]
  rw [hsub_eq]
  calc
    ‖∫ y in Ioi (0 : ℝ), ((deltaSpike ν ε y / y : ℝ) : ℂ) * (f (x / y) - f x)‖
      ≤ ∫ y in Ioi (0 : ℝ), ‖((deltaSpike ν ε y / y : ℝ) : ℂ) * (f (x / y) - f x)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ y in Ioi (0 : ℝ), M * (deltaSpike ν ε y / y) := by
        refine setIntegral_mono_on hint_diff.norm (hint_spike.const_mul M) measurableSet_Ioi
          fun y hy ↦ ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (div_nonneg (deltaSpike_nonneg hν0 hε.le y) hy.le)]
        by_cases hdy : deltaSpike ν ε y = 0
        · simp [hdy]
        · rw [mul_comm M]
          exact mul_le_mul_of_nonneg_left (hbd y (hsupp_spike hdy))
            (div_nonneg (deltaSpike_nonneg hν0 hε.le y) hy.le)
    _ = M := by rw [integral_const_mul, hmass, mul_one]

/-- Shared shrink-of-support step for pointwise and uniform approximate-identity convergence of
`mellinConv (deltaSpike ν ε) f`. -/
private lemma eventually_norm_mellinConv_deltaSpike_sub_lt {ν : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hν0 : ∀ x, 0 ≤ ν x) (hνs : Function.support ν ⊆ Icc a b)
    (hνm : ∫ x in Ioi (0 : ℝ), ν x / x = 1)
    {f : ℝ → ℂ} (hf : AEStronglyMeasurable f (volume.restrict (Ioi (0 : ℝ))))
    {K : Set ℝ} (hK_pos : K ⊆ Ioi (0 : ℝ)) {d δ η : ℝ} (hd : ∀ x ∈ K, x ≤ d) (hd0 : 0 < d)
    (hδ : 0 < δ) (hη : 0 < η)
    (hcont : ∀ x ∈ K, ∀ y ∈ Icc (min a 1) (max b 1), dist (x / y) x < δ →
      ‖f (x / y) - f x‖ ≤ η / 2) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ x ∈ K,
      ‖mellinConv (fun y ↦ (deltaSpike ν ε y : ℂ)) f x - f x‖ < η := by
  obtain ⟨x₀, hx₀⟩ := exists_ne_zero_of_integral_ne_zero (hνm ▸ one_ne_zero)
  have hx₀' : x₀ ∈ Icc a b := hνs (left_ne_zero_of_mul (div_eq_mul_inv (ν x₀) x₀ ▸ hx₀))
  have hb : 0 < b := ha.trans_le (hx₀'.1.trans hx₀'.2)
  have htend : Tendsto (fun ε : ℝ ↦ d * max |a ^ (-ε) - 1| |b ^ (-ε) - 1|) (𝓝[>] 0) (𝓝 0) := by
    have hca : Continuous fun ε : ℝ ↦ |a ^ (-ε) - 1| :=
      ((continuous_const.rpow continuous_neg (fun _ ↦ Or.inl ha.ne')).sub continuous_const).abs
    have hcb : Continuous fun ε : ℝ ↦ |b ^ (-ε) - 1| :=
      ((continuous_const.rpow continuous_neg (fun _ ↦ Or.inl hb.ne')).sub continuous_const).abs
    have hc : Continuous fun ε : ℝ ↦ d * max |a ^ (-ε) - 1| |b ^ (-ε) - 1| :=
      continuous_const.mul (hca.max hcb)
    have h0 : d * max |a ^ (-(0 : ℝ)) - 1| |b ^ (-(0 : ℝ)) - 1| = 0 := by simp
    exact (h0 ▸ hc.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one, htend.eventually (Iio_mem_nhds hδ)]
    with ε hε hεδ x hxK
  have hx0 : 0 < x := hK_pos hxK
  refine (norm_mellinConv_deltaSpike_sub_le ha hν0 hνs hνm hf hε.1 hx0 ?_).trans_lt
    (half_lt_self hη)
  intro y hy
  have hy_mem : y ∈ Icc (min a 1) (max b 1) := by
    refine ⟨le_trans ?_ hy.1, hy.2.trans ?_⟩
    · rcases le_or_gt 1 a with ha1 | ha1
      · exact (min_le_right a 1).trans (Real.one_le_rpow ha1 hε.1.le)
      · exact (min_le_left a 1).trans (by
          simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge ha ha1.le hε.2.le)
    · rcases le_or_gt 1 b with hb1 | hb1
      · have hb_le : b ^ ε ≤ b := by
          simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hb1 hε.2.le
        exact hb_le.trans (le_max_left b 1)
      · exact (Real.rpow_le_one hb.le hb1.le hε.1.le).trans (le_max_right b 1)
  have hinv : |y⁻¹ - 1| ≤ max |a ^ (-ε) - 1| |b ^ (-ε) - 1| := by
    have hlo : b ^ (-ε) ≤ y⁻¹ := by
      rw [Real.rpow_neg hb.le]
      exact inv_anti₀ ((Real.rpow_pos_of_pos ha ε).trans_le hy.1) hy.2
    have hhi : y⁻¹ ≤ a ^ (-ε) := by
      rw [Real.rpow_neg ha.le]
      exact inv_anti₀ (Real.rpow_pos_of_pos ha ε) hy.1
    exact abs_le.mpr
      ⟨by linarith [neg_abs_le (b ^ (-ε) - 1), le_max_right |a ^ (-ε) - 1| |b ^ (-ε) - 1|],
        by linarith [le_abs_self (a ^ (-ε) - 1), le_max_left |a ^ (-ε) - 1| |b ^ (-ε) - 1|]⟩
  have hdist : dist (x / y) x < δ := by
    have hsub : x / y - x = x * (y⁻¹ - 1) := by ring
    rw [Real.dist_eq, hsub, abs_mul, abs_of_pos hx0]
    exact (mul_le_mul (hd x hxK) hinv (abs_nonneg _) hd0.le).trans_lt hεδ
  exact hcont x hxK y hy_mem hdist

/-- Pointwise approximate identity for `dx / x`: if `ν ≥ 0` is supported in `[a, b] ⊂ (0, ∞)` with
`∫₀^∞ ν(x) dx / x = 1`, and `f : ℝ → ℂ` is `AEStronglyMeasurable` on `(0, ∞)` and continuous at
`x > 0`, then `mellinConv (deltaSpike ν ε) f x → f x` as `ε → 0⁺`. -/
theorem tendsto_mellinConv_deltaSpike {ν : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hν0 : ∀ x, 0 ≤ ν x)
    (hνs : Function.support ν ⊆ Icc a b) (hνm : ∫ x in Ioi (0 : ℝ), ν x / x = 1)
    {f : ℝ → ℂ} (hf : AEStronglyMeasurable f (volume.restrict (Ioi (0 : ℝ))))
    {x : ℝ} (hx : 0 < x) (hcont : ContinuousAt f x) :
    Tendsto (fun ε : ℝ ↦ mellinConv (fun y ↦ (deltaSpike ν ε y : ℂ)) f x) (𝓝[>] 0) (𝓝 (f x)) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨δ, hδ, hcontδ⟩ := Metric.continuousAt_iff.mp hcont (η / 2) (half_pos hη)
  have hev := eventually_norm_mellinConv_deltaSpike_sub_lt ha hν0 hνs hνm hf
    (K := {x}) (singleton_subset_iff.mpr hx) (d := x) (fun _ h ↦ (mem_singleton_iff.mp h).le)
    hx hδ hη fun z hz y _ hdist ↦ by
      rw [mem_singleton_iff.mp hz] at hdist ⊢
      rw [← dist_eq_norm]
      exact (hcontδ hdist).le
  filter_upwards [hev] with ε hε
  rw [dist_eq_norm]
  exact hε x (mem_singleton x)

/-- Uniform approximate identity on compact subsets of `(0, ∞)`: if `ν ≥ 0` is supported in
`[a, b] ⊂ (0, ∞)` with `∫₀^∞ ν(x) dx / x = 1`, `f : ℝ → ℂ` is continuous on `(0, ∞)`, and
`K ⊆ (0, ∞)` is compact, then `mellinConv (deltaSpike ν ε) f → f` uniformly on `K` as `ε → 0⁺`. -/
theorem tendstoUniformlyOn_mellinConv_deltaSpike {ν : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hν0 : ∀ x, 0 ≤ ν x) (hνs : Function.support ν ⊆ Icc a b)
    (hνm : ∫ x in Ioi (0 : ℝ), ν x / x = 1)
    {f : ℝ → ℂ} (hf : ContinuousOn f (Ioi (0 : ℝ))) {K : Set ℝ} (hK : IsCompact K)
    (hK_sub : K ⊆ Ioi (0 : ℝ)) :
    TendstoUniformlyOn (fun ε x ↦ mellinConv (fun y ↦ (deltaSpike ν ε y : ℂ)) f x) f
      (𝓝[>] 0) K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact Eventually.of_forall fun _ _ h ↦ False.elim h
  obtain ⟨c, hcK, hc_min⟩ := hK.exists_isMinOn hKne continuousOn_id
  obtain ⟨d, hdK, hd_max⟩ := hK.exists_isMaxOn hKne continuousOn_id
  have hc : 0 < c := hK_sub hcK
  have hd : 0 < d := hK_sub hdK
  have hmin_pos : 0 < min a 1 := lt_min ha zero_lt_one
  have hmax_pos : 0 < max b 1 := lt_of_lt_of_le zero_lt_one (le_max_right b 1)
  set L := Icc (c / max b 1) (d / min a 1)
  have hunif : UniformContinuousOn f L :=
    isCompact_Icc.uniformContinuousOn_of_continuous
      (hf.mono fun _ hz ↦ (div_pos hc hmax_pos).trans_le hz.1)
  obtain ⟨δ, hδ, hδ_unif⟩ := Metric.uniformContinuousOn_iff.mp hunif (η / 2) (half_pos hη)
  have hev := eventually_norm_mellinConv_deltaSpike_sub_lt ha hν0 hνs hνm
    (hf.aestronglyMeasurable measurableSet_Ioi) hK_sub hd_max hd hδ hη fun x hxK y hy hdist ↦ by
      have hx0 : 0 < x := hK_sub hxK
      have hxL : x ∈ L :=
        ⟨(div_le_self hc.le (le_max_right b 1)).trans (hc_min hxK),
          (hd_max hxK).trans (le_div_self hd.le hmin_pos (min_le_right a 1))⟩
      have hxyL : x / y ∈ L :=
        ⟨div_le_div₀ hx0.le (hc_min hxK) (hmin_pos.trans_le hy.1) hy.2,
          div_le_div₀ hd.le (hd_max hxK) hmin_pos hy.1⟩
      rw [← dist_eq_norm]
      exact (hδ_unif (x / y) hxyL x hxL hdist).le
  filter_upwards [hev] with ε hε x hxK
  rw [dist_comm, dist_eq_norm]
  exact hε x hxK

/-! ### Smoothed cutoffs -/

/-- The smoothed cutoff associated to a bump `ν : ℝ → ℝ` and scale `ε : ℝ`:
`smoothCutoff ν ε x = ∫ z in Ioi x, deltaSpike ν ε z / z` for `x > 0` and `0` for `x ≤ 0`. -/
noncomputable def smoothCutoff (ν : ℝ → ℝ) (ε x : ℝ) : ℝ :=
  if 0 < x then ∫ z in Ioi x, deltaSpike ν ε z / z else 0

/-- Definitional unfolding of `smoothCutoff`. -/
theorem smoothCutoff_def (ν : ℝ → ℝ) (ε x : ℝ) :
    smoothCutoff ν ε x = if 0 < x then ∫ z in Ioi x, deltaSpike ν ε z / z else 0 := (rfl)

@[simp]
theorem smoothCutoff_of_pos {ν : ℝ → ℝ} {ε x : ℝ} (hx : 0 < x) :
    smoothCutoff ν ε x = ∫ z in Ioi x, deltaSpike ν ε z / z := by
  simp [smoothCutoff_def, hx]

@[simp]
theorem smoothCutoff_of_nonpos {ν : ℝ → ℝ} {ε x : ℝ} (hx : x ≤ 0) :
    smoothCutoff ν ε x = 0 := by
  simp [smoothCutoff_def, hx.not_gt]

/-- `smoothCutoff` vanishes at `0`. -/
theorem smoothCutoff_zero (ν : ℝ → ℝ) (ε : ℝ) : smoothCutoff ν ε 0 = 0 :=
  smoothCutoff_of_nonpos le_rfl

/-- For `x > 0`, `smoothCutoff ν ε x` equals the Mellin convolution of `(Ioc 0 1).indicator 1`
with `deltaSpike ν ε`, with no integrability or bump hypothesis. -/
theorem smoothCutoff_eq_mellinConv (ν : ℝ → ℝ) (ε : ℝ) {x : ℝ} (hx : 0 < x) :
    (smoothCutoff ν ε x : ℂ) =
      mellinConv ((Ioc (0 : ℝ) 1).indicator 1) (fun y ↦ (deltaSpike ν ε y : ℂ)) x := by
  rw [mellinConv_comm _ _ hx, mellinConv_def, smoothCutoff_of_pos hx, ← integral_complex_ofReal]
  have hcongr : (∫ y in Ioi (0 : ℝ),
      (deltaSpike ν ε y : ℂ) * (Ioc (0 : ℝ) 1).indicator 1 (x / y) / y) =
      ∫ y in Ioi (0 : ℝ), (Ici x).indicator (fun y : ℝ ↦ ((deltaSpike ν ε y / y : ℝ) : ℂ)) y := by
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_
    have hy0 : 0 < y := hy
    have hiff : x / y ∈ Ioc (0 : ℝ) 1 ↔ y ∈ Ici x := by
      simp only [mem_Ioc, mem_Ici, div_pos_iff_of_pos_left hx, div_le_one hy0, hy0, true_and]
    by_cases hxy : y ∈ Ici x
    · rw [indicator_of_mem (hiff.mpr hxy), indicator_of_mem hxy]
      simp [ofReal_div]
    · rw [indicator_of_notMem (mt hiff.mp hxy), indicator_of_notMem hxy]
      simp
  rw [hcongr, setIntegral_indicator measurableSet_Ici,
    inter_eq_right.mpr (Ici_subset_Ioi.mpr hx), MeasureTheory.integral_Ici_eq_integral_Ioi]

/-- Nonnegativity of `smoothCutoff` for nonnegative `ν` and `ε ≥ 0`. -/
theorem smoothCutoff_nonneg {ν : ℝ → ℝ} (hν0 : ∀ x, 0 ≤ ν x) {ε : ℝ} (hε : 0 ≤ ε) (x : ℝ) :
    0 ≤ smoothCutoff ν ε x := by
  rw [smoothCutoff_def]
  split_ifs with hx
  · exact setIntegral_nonneg measurableSet_Ioi fun z hz ↦
      div_nonneg (deltaSpike_nonneg hν0 hε z) (hx.trans hz).le
  · exact le_rfl

/-- Upper bound `smoothCutoff ν ε x ≤ 1` for nonnegative `ν` with `dx / x`-mass `1` and `ε > 0`. -/
theorem smoothCutoff_le_one {ν : ℝ → ℝ} (hν0 : ∀ x, 0 ≤ ν x)
    (hνm : ∫ x in Ioi (0 : ℝ), ν x / x = 1) {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    smoothCutoff ν ε x ≤ 1 := by
  rw [smoothCutoff_def]
  split_ifs with hx
  · have hint : IntegrableOn (fun z ↦ deltaSpike ν ε z / z) (Ioi (0 : ℝ)) :=
      (integrableOn_deltaSpike_div_iff hε).mpr (integrable_of_integral_eq_one hνm)
    have hmono := setIntegral_mono_set hint
      ((ae_restrict_mem measurableSet_Ioi).mono fun z hz ↦
        div_nonneg (deltaSpike_nonneg hν0 hε.le z) (le_of_lt hz))
      (Eventually.of_forall (Ioi_subset_Ioi hx.le))
    rwa [integral_deltaSpike_div ν hε, hνm] at hmono
  · exact zero_le_one

/-- `smoothCutoff ν ε` is antitone on `(0, ∞)` whenever `ν ≥ 0` and `ν x / x` is integrable on
`(0, ∞)`. -/
theorem smoothCutoff_antitoneOn {ν : ℝ → ℝ} (hν0 : ∀ x, 0 ≤ ν x)
    (hνi : IntegrableOn (fun x ↦ ν x / x) (Ioi (0 : ℝ))) {ε : ℝ} (hε : 0 < ε) :
    AntitoneOn (smoothCutoff ν ε) (Ioi (0 : ℝ)) := by
  intro x hx y hy hxy
  rw [smoothCutoff_of_pos hx, smoothCutoff_of_pos hy]
  have hint : IntegrableOn (fun z ↦ deltaSpike ν ε z / z) (Ioi x) :=
    ((integrableOn_deltaSpike_div_iff hε).mpr hνi).mono_set (Ioi_subset_Ioi hx.le)
  exact setIntegral_mono_set hint
    ((ae_restrict_mem measurableSet_Ioi).mono fun z hz ↦
      div_nonneg (deltaSpike_nonneg hν0 hε.le z) (hx.trans hz).le)
    (Eventually.of_forall (Ioi_subset_Ioi hxy))

/-- Plateau at `1`: for `ν` supported in `[a, b]` with `0 < a` and `dx / x`-mass `1`,
`smoothCutoff ν ε x = 1` for all `0 < x ≤ a ^ ε`. -/
theorem smoothCutoff_eq_one {ν : ℝ → ℝ} {a b ε x : ℝ} (ha : 0 < a)
    (hνs : Function.support ν ⊆ Icc a b) (hνm : ∫ x in Ioi (0 : ℝ), ν x / x = 1)
    (hε : 0 < ε) (hx0 : 0 < x) (hx : x ≤ a ^ ε) :
    smoothCutoff ν ε x = 1 := by
  have hsupp := support_deltaSpike_subset_Icc ha hε hνs
  rw [smoothCutoff_of_pos hx0]
  have heq : (∫ z in Ioi x, deltaSpike ν ε z / z) = ∫ z in Ioi (0 : ℝ), deltaSpike ν ε z / z := by
    refine (setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Ioi.nullMeasurableSet
      (Ioi_subset_Ioi hx0.le) ?_).symm
    have hae_ne : ∀ᵐ z : ℝ ∂volume, z ≠ x := by rw [ae_iff]; simp
    filter_upwards [hae_ne] with z hzx hzdiff
    have hlt : z < x := lt_of_le_of_ne (le_of_not_gt hzdiff.2) hzx
    have hdz : deltaSpike ν ε z = 0 :=
      Function.notMem_support.mp fun h ↦ (hlt.trans_le hx).not_ge (hsupp h).1
    simp [hdz]
  rw [heq, integral_deltaSpike_div ν hε, hνm]

/-- Plateau at `0`: for `ν` supported in `[a, b]` with `0 < a`, `smoothCutoff ν ε x = 0` for all
`b ^ ε ≤ x`. -/
theorem smoothCutoff_eq_zero_of_le {ν : ℝ → ℝ} {a b ε x : ℝ} (ha : 0 < a)
    (hνs : Function.support ν ⊆ Icc a b) (hε : 0 < ε) (hx : b ^ ε ≤ x) :
    smoothCutoff ν ε x = 0 := by
  by_cases hx0 : 0 < x
  · have hsupp := support_deltaSpike_subset_Icc ha hε hνs
    rw [smoothCutoff_of_pos hx0]
    refine setIntegral_eq_zero_of_forall_eq_zero fun z hz ↦ ?_
    have hdz : deltaSpike ν ε z = 0 :=
      Function.notMem_support.mp fun h ↦ (hx.trans_lt hz).not_ge (hsupp h).2
    simp [hdz]
  · exact smoothCutoff_of_nonpos (le_of_not_gt hx0)

/-- For a multiplicatively symmetric bump (`ν x⁻¹ = ν x` on `(0, ∞)`) of `dx / x`-mass `1`,
`smoothCutoff ν ε 1 = 1 / 2`. -/
theorem smoothCutoff_one_of_symm {ν : ℝ → ℝ} (hsym : ∀ x, 0 < x → ν x⁻¹ = ν x)
    (hνm : ∫ x in Ioi (0 : ℝ), ν x / x = 1) {ε : ℝ} (hε : 0 < ε) :
    smoothCutoff ν ε 1 = 1 / 2 := by
  have hint : IntegrableOn (fun z ↦ deltaSpike ν ε z / z) (Ioi (0 : ℝ)) :=
    (integrableOn_deltaSpike_div_iff hε).mpr (integrable_of_integral_eq_one hνm)
  have hsplit : (∫ z in Ioi (0 : ℝ), deltaSpike ν ε z / z) =
      (∫ z in Ioc (0 : ℝ) 1, deltaSpike ν ε z / z) +
        (∫ z in Ioi (1 : ℝ), deltaSpike ν ε z / z) := by
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, setIntegral_union Ioc_disjoint_Ioi_same
      measurableSet_Ioi (hint.mono_set Ioc_subset_Ioi_self)
      (hint.mono_set (Ioi_subset_Ioi zero_le_one))]
  have hinv := mellin_comp_inv
    (fun z : ℝ ↦ (((Ioi (1 : ℝ)).indicator (deltaSpike ν ε) z : ℝ) : ℂ)) 0
  rw [neg_zero, mellin_ofReal_zero, mellin_ofReal_zero] at hinv
  have hinv_real := Complex.ofReal_injective hinv
  have hright : (∫ z in Ioi (0 : ℝ), (Ioi (1 : ℝ)).indicator (deltaSpike ν ε) z / z) =
      ∫ z in Ioi (1 : ℝ), deltaSpike ν ε z / z := by
    have hcongr_r : (∫ z in Ioi (0 : ℝ), (Ioi (1 : ℝ)).indicator (deltaSpike ν ε) z / z) =
        ∫ z in Ioi (0 : ℝ), (Ioi (1 : ℝ)).indicator (fun z ↦ deltaSpike ν ε z / z) z :=
      setIntegral_congr_fun measurableSet_Ioi fun z _ ↦ by
        by_cases hz : z ∈ Ioi (1 : ℝ) <;> simp [hz]
    rw [hcongr_r, setIntegral_indicator measurableSet_Ioi,
      inter_eq_right.mpr (Ioi_subset_Ioi zero_le_one)]
  have hleft : (∫ z in Ioi (0 : ℝ), (Ioi (1 : ℝ)).indicator (deltaSpike ν ε) z⁻¹ / z) =
      ∫ z in Ioc (0 : ℝ) 1, deltaSpike ν ε z / z := by
    have hcongr : (∫ z in Ioi (0 : ℝ), (Ioi (1 : ℝ)).indicator (deltaSpike ν ε) z⁻¹ / z) =
        ∫ z in Ioi (0 : ℝ), (Ioo (0 : ℝ) 1).indicator (fun z ↦ deltaSpike ν ε z / z) z := by
      refine setIntegral_congr_fun measurableSet_Ioi fun z hz ↦ ?_
      have hz0 : 0 < z := hz
      have hiff : z⁻¹ ∈ Ioi (1 : ℝ) ↔ z ∈ Ioo (0 : ℝ) 1 := by
        simp [mem_Ioi, mem_Ioo, hz0, one_lt_inv₀ hz0]
      by_cases hz1 : z ∈ Ioo (0 : ℝ) 1
      · rw [indicator_of_mem (hiff.mpr hz1), indicator_of_mem hz1,
          deltaSpike_inv_of_symm hsym ε hz0]
      · rw [indicator_of_notMem (mt hiff.mp hz1), indicator_of_notMem hz1, zero_div]
    rw [hcongr, setIntegral_indicator measurableSet_Ioo, inter_eq_right.mpr Ioo_subset_Ioi_self,
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [hleft, hright] at hinv_real
  rw [integral_deltaSpike_div ν hε, hνm, hinv_real] at hsplit
  rw [smoothCutoff_of_pos one_pos]
  linarith

/-- Continuity of `smoothCutoff ν ε` on `(0, ∞)` whenever `ν x / x` is integrable on `(0, ∞)`
and `ε > 0`. -/
theorem continuousOn_smoothCutoff {ν : ℝ → ℝ}
    (hνi : IntegrableOn (fun x ↦ ν x / x) (Ioi (0 : ℝ))) {ε : ℝ} (hε : 0 < ε) :
    ContinuousOn (smoothCutoff ν ε) (Ioi (0 : ℝ)) := by
  have hint : IntegrableOn (fun z ↦ deltaSpike ν ε z / z) (Ioi (0 : ℝ)) :=
    (integrableOn_deltaSpike_div_iff hε).mpr hνi
  set G : ℝ → ℝ := (Ioi (0 : ℝ)).indicator (fun z ↦ deltaSpike ν ε z / z)
  have hG_int : Integrable G := (integrable_indicator_iff measurableSet_Ioi).mpr hint
  have hcont_prim : Continuous fun x : ℝ ↦
      (∫ z in Ioi (0 : ℝ), deltaSpike ν ε z / z) - ∫ z in (0 : ℝ)..x, G z :=
    continuous_const.sub
      (intervalIntegral.continuous_primitive (fun _ _ ↦ hG_int.intervalIntegrable) 0)
  refine hcont_prim.continuousOn.congr fun x hx ↦ ?_
  have hx0 : 0 < x := hx
  dsimp only
  rw [smoothCutoff_of_pos hx0, intervalIntegral.integral_of_le hx0.le]
  have hIoc : (∫ z in Ioc (0 : ℝ) x, G z) = ∫ z in Ioc (0 : ℝ) x, deltaSpike ν ε z / z :=
    setIntegral_congr_fun measurableSet_Ioc fun z hz ↦ indicator_of_mem hz.1 _
  have hsplit : (∫ z in Ioi (0 : ℝ), deltaSpike ν ε z / z) =
      (∫ z in Ioc (0 : ℝ) x, deltaSpike ν ε z / z) +
        (∫ z in Ioi x, deltaSpike ν ε z / z) := by
    rw [← Ioc_union_Ioi_eq_Ioi hx0.le, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi hx0.le))]
  linarith

/-- For `ε > 0`, `Re s > 0`, and `MellinConvergent ν (ε * s)`, the smoothed cutoff
`smoothCutoff ν ε` has absolutely convergent Mellin transform `mellin ν (ε * s) / s`. -/
theorem hasMellin_smoothCutoff {ν : ℝ → ℝ} {ε : ℝ} {s : ℂ} (hε : 0 < ε) (hs : 0 < s.re)
    (hν : MellinConvergent (fun x ↦ (ν x : ℂ)) (ε * s)) :
    HasMellin (fun x ↦ (smoothCutoff ν ε x : ℂ)) s
      (mellin (fun x ↦ (ν x : ℂ)) (ε * s) / s) := by
  have h1 : HasMellin ((Ioc (0 : ℝ) 1).indicator (1 : ℝ → ℂ)) s (1 / s) := hasMellin_one_Ioc hs
  have h2 : MellinConvergent (fun x ↦ (deltaSpike ν ε x : ℂ)) s :=
    (mellinConvergent_deltaSpike_iff hε s).mpr hν
  have hconv := hasMellin_integral_mul_div h1.1 h2
  rw [h1.2, mellin_deltaSpike ν hε s, one_div_mul_eq_div] at hconv
  refine ⟨?_, ?_⟩
  · refine hconv.1.congr_fun (fun x hx ↦ ?_) measurableSet_Ioi
    dsimp only
    rw [smoothCutoff_eq_mellinConv ν ε hx, mellinConv_def]
  · rw [← hconv.2]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
    dsimp only
    rw [smoothCutoff_eq_mellinConv ν ε hx, mellinConv_def]

/-- Mellin transform of the smoothed cutoff: for `ε > 0`, `Re s > 0`, and
`MellinConvergent ν (ε * s)`, `mellin (smoothCutoff ν ε) s = mellin ν (ε * s) / s`. -/
theorem mellin_smoothCutoff {ν : ℝ → ℝ} {ε : ℝ} {s : ℂ} (hε : 0 < ε) (hs : 0 < s.re)
    (hν : MellinConvergent (fun x ↦ (ν x : ℂ)) (ε * s)) :
    mellin (fun x ↦ (smoothCutoff ν ε x : ℂ)) s = mellin (fun x ↦ (ν x : ℂ)) (ε * s) / s :=
  (hasMellin_smoothCutoff hε hs hν).2

/-- Uniform-in-`ε` vertical-strip decay of the Mellin transform of `smoothCutoff ν ε`: if `ν` is
`C^k` on `(0, ∞)` and supported in `[a, b] ⊂ (0, ∞)`, then for every `σ₁ > 0` and `σ₂` there is
`C ≥ 0` such that `‖mellin (smoothCutoff ν ε) s‖ ≤ C / (‖s‖ * (1 + ε * ‖s‖) ^ k)` for all
`0 < ε ≤ 1` and `σ₁ ≤ Re s ≤ σ₂`. -/
theorem norm_mellin_smoothCutoff_le {ν : ℝ → ℝ} {a b σ₁ σ₂ : ℝ} {k : ℕ} (ha : 0 < a)
    (hsupp : Function.support ν ⊆ Icc a b) (hν : ContDiffOn ℝ k ν (Ioi (0 : ℝ)))
    (hσ₁ : 0 < σ₁) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
      ‖mellin (fun x ↦ (smoothCutoff ν ε x : ℂ)) s‖ ≤ C / (‖s‖ * (1 + ε * ‖s‖) ^ k) := by
  have hνc : ContDiffOn ℝ k (fun x ↦ (ν x : ℂ)) (Ioi (0 : ℝ)) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hν
  have hsuppc : Function.support (fun x ↦ (ν x : ℂ)) ⊆ Icc a b :=
    fun x hx ↦ hsupp fun h ↦ hx (by simp [h])
  have hloc : LocallyIntegrableOn (fun x ↦ (ν x : ℂ)) (Ioi (0 : ℝ)) :=
    hνc.continuousOn.locallyIntegrableOn measurableSet_Ioi
  obtain ⟨C, hC0, hC⟩ := exists_norm_mellin_le_of_contDiffOn_of_support_subset_Icc
    (σ₁ := 0) (σ₂ := max σ₂ 0) ha hsuppc hνc
  refine ⟨C, hC0, fun ε hε0 hε1 s hs₁ hs₂ ↦ ?_⟩
  have hs_pos : 0 < s.re := hσ₁.trans_le hs₁
  have hεs_re₁ : 0 ≤ ((ε : ℂ) * s).re := by
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg hε0.le hs_pos.le
  have hεs_re₂ : ((ε : ℂ) * s).re ≤ max σ₂ 0 := by
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    exact (mul_le_of_le_one_left hs_pos.le hε1).trans (hs₂.trans (le_max_left σ₂ 0))
  have hbd := hC ((ε : ℂ) * s) hεs_re₁ hεs_re₂
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε0] at hbd
  rw [mellin_smoothCutoff hε0 hs_pos
    (mellinConvergent_of_support_subset_Icc ha hsuppc hloc ((ε : ℂ) * s)), norm_div,
    div_mul_eq_div_div, div_right_comm]
  exact div_le_div_of_nonneg_right hbd (norm_nonneg s)

/-- Vertical integrability of `mellin (smoothCutoff ν ε)` on `Re s = σ > 0` for any `C^k` bump
`ν` (`k ≥ 1`) supported in `[a, b] ⊂ (0, ∞)` and any `ε > 0`. -/
theorem verticalIntegrable_mellin_smoothCutoff {ν : ℝ → ℝ} {a b ε σ : ℝ} {k : ℕ} (hk : 1 ≤ k)
    (ha : 0 < a) (hsupp : Function.support ν ⊆ Icc a b) (hν : ContDiffOn ℝ k ν (Ioi (0 : ℝ)))
    (hε : 0 < ε) (hσ : 0 < σ) :
    VerticalIntegrable (mellin (fun x ↦ (smoothCutoff ν ε x : ℂ))) σ := by
  have hνc : ContDiffOn ℝ 1 (fun x ↦ (ν x : ℂ)) (Ioi (0 : ℝ)) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (hν.of_le (by exact_mod_cast hk))
  have hsuppc : Function.support (fun x ↦ (ν x : ℂ)) ⊆ Icc a b :=
    fun x hx ↦ hsupp fun h ↦ hx (by simp [h])
  have hloc : LocallyIntegrableOn (fun x ↦ (ν x : ℂ)) (Ioi (0 : ℝ)) :=
    hνc.continuousOn.locallyIntegrableOn measurableSet_Ioi
  obtain ⟨C, hC0, hC⟩ := exists_norm_mellin_le_of_contDiffOn_of_support_subset_Icc
    (σ₁ := ε * σ) (σ₂ := ε * σ) ha hsuppc hνc
  have hline : ∀ t : ℝ, mellin (fun x ↦ (smoothCutoff ν ε x : ℂ)) ((σ : ℂ) + t * I) =
      mellin (fun x ↦ (ν x : ℂ)) ((ε : ℂ) * ((σ : ℂ) + t * I)) / ((σ : ℂ) + t * I) := fun t ↦
    mellin_smoothCutoff hε (by simp [hσ])
      (mellinConvergent_of_support_subset_Icc ha hsuppc hloc _)
  have hcont : Continuous fun t : ℝ ↦
      mellin (fun x ↦ (smoothCutoff ν ε x : ℂ)) ((σ : ℂ) + t * I) := by
    simp_rw [hline]
    have hdiff := differentiable_mellin_of_support_subset_Icc ha hsuppc hloc
    have hline_cont : Continuous fun t : ℝ ↦ (σ : ℂ) + t * I :=
      continuous_const.add (continuous_ofReal.mul continuous_const)
    refine (hdiff.continuous.comp (continuous_const.mul hline_cont)).div hline_cont fun t h0 ↦ ?_
    have := congrArg Complex.re h0
    simp at this
    linarith
  have hm_pos : 0 < min σ ε := lt_min hσ hε
  refine (integrable_inv_one_add_sq.const_mul (C / min σ ε)).mono' hcont.aestronglyMeasurable
    (Eventually.of_forall fun t ↦ ?_)
  set s : ℂ := (σ : ℂ) + t * I
  have hεs_re : ((ε : ℂ) * s).re = ε * σ := by simp [s]
  have hbd := hC ((ε : ℂ) * s) hεs_re.ge hεs_re.le
  rw [pow_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε] at hbd
  rw [hline t, norm_div]
  have hre : σ ≤ ‖s‖ := by simpa [s, abs_of_pos hσ] using Complex.abs_re_le_norm s
  have him : |t| ≤ ‖s‖ := by simpa [s] using Complex.abs_im_le_norm s
  have hsq : t ^ 2 ≤ ‖s‖ ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg t) him 2
  have hdenom : min σ ε * (1 + t ^ 2) ≤ ‖s‖ * (1 + ε * ‖s‖) := by
    have h1 : min σ ε ≤ ‖s‖ := (min_le_left σ ε).trans hre
    have h2 : min σ ε * t ^ 2 ≤ ε * ‖s‖ ^ 2 :=
      mul_le_mul (min_le_right σ ε) hsq (sq_nonneg t) hε.le
    nlinarith
  calc
    ‖mellin (fun x ↦ (ν x : ℂ)) ((ε : ℂ) * s)‖ / ‖s‖
      ≤ (C / (1 + ε * ‖s‖)) / ‖s‖ := div_le_div_of_nonneg_right hbd (norm_nonneg s)
    _ = C / (‖s‖ * (1 + ε * ‖s‖)) := by rw [div_div, mul_comm]
    _ ≤ C / (min σ ε * (1 + t ^ 2)) :=
        div_le_div_of_nonneg_left hC0 (mul_pos hm_pos (by positivity)) hdenom
    _ = C / min σ ε * (1 + t ^ 2)⁻¹ := by rw [div_mul_eq_div_div, div_eq_mul_inv]

/-- For a nonnegative bump `ν` supported in `[a, b] ⊂ (0, ∞)` with `∫₀^∞ ν(x) dx / x = 1` and
`0 < ε ≤ 1`, `‖mellin (smoothCutoff ν ε) 1 - 1‖ ≤ max b 1 * max |log a| |log b| * ε`. -/
theorem norm_mellin_smoothCutoff_one_sub_one_le {ν : ℝ → ℝ} {a b ε : ℝ} (ha : 0 < a)
    (hν0 : ∀ x, 0 ≤ ν x) (hνs : Function.support ν ⊆ Icc a b)
    (hνm : ∫ x in Ioi (0 : ℝ), ν x / x = 1) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ‖mellin (fun x ↦ (smoothCutoff ν ε x : ℂ)) 1 - 1‖ ≤
      max b 1 * max |Real.log a| |Real.log b| * ε := by
  have hconv0 : MellinConvergent (fun x ↦ (ν x : ℂ)) 0 :=
    (mellinConvergent_ofReal_zero_iff ν).mpr (integrable_of_integral_eq_one hνm)
  have hconv : MellinConvergent (fun x ↦ (ν x : ℂ)) ((ε : ℂ) * 1) :=
    hconv0.of_support_subset_Icc ha (fun x hx ↦ hνs fun h ↦ hx (by simp [h])) ((ε : ℂ) * 1)
  rw [mellin_smoothCutoff hε0 (by simp) hconv, mul_one, div_one]
  exact norm_mellin_ofReal_sub_one_le ha hν0 hνs hνm hε0.le hε1

/-! ### Existence of a symmetric smooth bump -/

/-- For every `R > 1`, there exists a `C^∞`, nonnegative, multiplicatively symmetric bump function
`ν : ℝ → ℝ` supported in `[R⁻¹, R]` with `∫₀^∞ ν(x) dx / x = 1`. -/
theorem exists_smooth_symmetric_bump {R : ℝ} (hR : 1 < R) :
    ∃ ν : ℝ → ℝ, ContDiff ℝ ∞ ν ∧ (∀ x, 0 ≤ ν x) ∧
      Function.support ν ⊆ Icc R⁻¹ R ∧ (∫ x in Ioi (0 : ℝ), ν x / x = 1) ∧
      ∀ x, 0 < x → ν x⁻¹ = ν x := by
  have hR0 : 0 < R := zero_lt_one.trans hR
  have hlogR : 0 < Real.log R := Real.log_pos hR
  let b : ContDiffBump (0 : ℝ) := ⟨Real.log R / 4, Real.log R / 2, by positivity, by linarith⟩
  let ν : ℝ → ℝ := fun x ↦ if 0 < x then b.normed volume (Real.log x) else 0
  have hsupp : Function.support ν ⊆ Icc R⁻¹ R := by
    intro x hx
    have hx0 : 0 < x := by by_contra h; exact hx (by simp [ν, h])
    have hbx : Real.log x ∈ Function.support (b.normed volume) := by simpa [ν, hx0] using hx
    rw [b.support_normed_eq, Metric.mem_ball, Real.dist_eq, sub_zero] at hbx
    have habs : |Real.log x| ≤ Real.log R := le_of_lt (hbx.trans (by dsimp [b]; linarith))
    obtain ⟨hlo, hhi⟩ := abs_le.mp habs
    refine ⟨?_, ?_⟩
    · rw [← Real.exp_log hx0, ← Real.exp_log hR0, ← Real.exp_neg]
      exact Real.exp_le_exp.mpr hlo
    · rw [← Real.exp_log hx0, ← Real.exp_log hR0]
      exact Real.exp_le_exp.mpr hhi
  have hcd : ContDiff ℝ ∞ ν := by
    rw [contDiff_iff_contDiffAt]
    intro x
    rcases lt_or_ge 0 x with hx | hx
    · have hpos : ContDiffOn ℝ ∞ (fun t : ℝ ↦ b.normed volume (Real.log t)) (Ioi (0 : ℝ)) :=
        b.contDiff_normed.comp_contDiffOn (Real.contDiffOn_log.mono fun _ ht ↦ ne_of_gt ht)
      have heq : ν =ᶠ[𝓝 x] fun t : ℝ ↦ b.normed volume (Real.log t) := by
        filter_upwards [Ioi_mem_nhds hx] with t ht
        have ht0 : 0 < t := ht
        simp [ν, ht0]
      exact (hpos.contDiffAt (Ioi_mem_nhds hx)).congr_of_eventuallyEq heq
    · have heq : ν =ᶠ[𝓝 x] fun _ : ℝ ↦ (0 : ℝ) := by
        filter_upwards [Iio_mem_nhds (hx.trans_lt (inv_pos.mpr hR0))] with t ht
        exact Function.notMem_support.mp fun h ↦ ht.not_ge (hsupp h).1
      exact contDiffAt_const.congr_of_eventuallyEq heq
  have hnonneg : ∀ x, 0 ≤ ν x := fun x ↦ by
    dsimp only [ν]; split_ifs; exacts [b.nonneg_normed _, le_rfl]
  have hmass : ∫ x in Ioi (0 : ℝ), ν x / x = 1 := by
    rw [← integral_comp_exp]
    have hEq : (fun t : ℝ ↦ Real.exp t • (ν (Real.exp t) / Real.exp t)) = b.normed volume := by
      ext t
      simp only [ν, Real.exp_pos, ↓reduceIte, Real.log_exp, smul_eq_mul,
        mul_div_cancel₀ _ (Real.exp_ne_zero t)]
    rw [hEq, b.integral_normed]
  have hsym : ∀ x, 0 < x → ν x⁻¹ = ν x := fun x hx ↦ by
    simp only [ν, inv_pos.mpr hx, hx, ↓reduceIte, Real.log_inv, b.normed_neg]
  exact ⟨ν, hcd, hnonneg, hsupp, hmass, hsym⟩

end TauCeti
