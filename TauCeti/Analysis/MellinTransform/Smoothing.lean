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

/-!
# Delta spikes and smoothed cutoffs for Mellin transforms

This file develops multiplicative smoothing on `(0, ∞)` using rescaled bump functions (delta
spikes) and smoothed step functions (smoothed cutoffs).

For a bump `ν : ℝ → ℝ` and scale `ε > 0`, the delta spike
`deltaSpike ν ε x = ε⁻¹ * ν (x ^ ε⁻¹)` (for `x > 0`, and `0` for `x ≤ 0`) rescales
`Function.support ν ∩ Ioi 0 ⊆ Icc a b` (`0 < a`) to `[a ^ ε, b ^ ε]`, preserves the
multiplicative Haar mass `∫₀^∞ ν(x) dx / x`, and satisfies
`mellin (deltaSpike ν ε) s = mellin ν (ε * s)`. When `ν ≥ 0` on `(0, ∞)` satisfies
`Function.support ν ∩ Ioi 0 ⊆ Icc a b` (`0 < a`) with `∫₀^∞ ν(x) dx / x = 1`, convolution with
`deltaSpike ν ε` forms an approximate identity for `dx / x` (pointwise for `f`
`AEStronglyMeasurable` on `(0, ∞)` and continuous at `x > 0`, and uniformly on compact subsets of
`(0, ∞)` for `f` continuous on `(0, ∞)`), and
`‖mellin (deltaSpike ν ε) 1 - 1‖ ≤ max b 1 * max |log a| |log b| * ε` for `0 < ε ≤ 1`.

The smoothed cutoff `smoothCutoff ν ε x = ∫_{(x, ∞)} deltaSpike ν ε z dz / z` (for `x > 0`, and
`0` for `x ≤ 0`) equals `mellinConv ((Ioc 0 1).indicator 1) (deltaSpike ν ε)` on `(0, ∞)` for
every `ε : ℝ`. For `ε > 0` and a bump `ν ≥ 0` on `(0, ∞)` with `dx / x`-mass `1`, it satisfies
`0 ≤ smoothCutoff ν ε ≤ 1` and is antitone on `(0, ∞)`. For `ε > 0`, it equals `1` on
`(0, a ^ ε]` when `Function.support ν ∩ Ioi 0 ⊆ Ici a` (`0 < a`), `0` on `[b ^ ε, ∞)` when
`Function.support ν ∩ Ioi 0 ⊆ Iic b`, `1 / 2` at `x = 1` when `ν (x⁻¹) = ν x` on `(0, ∞)`, is
continuous on `(0, ∞)` whenever `ν x / x` is integrable on `(0, ∞)`, and has Mellin transform
`mellin ν (ε * s) / s` for `Re s > 0` when `MellinConvergent ν (ε * s)`. When `ν` is `C^k` on
`(0, ∞)` with `Function.support ν ∩ Ioi 0 ⊆ Icc a b` (`0 < a`), this gives the uniform-in-`ε`
decay bound `‖mellin (smoothCutoff ν ε) s‖ ≤ C / (‖s‖ * (1 + ε * ‖s‖) ^ k)` for `0 < ε ≤ 1` and
`0 < Re s ≤ σ₂`, and vertical integrability on `Re s = σ > 0` for every `ε > 0` when `ν` is `C^1`
on `(0, ∞)`.

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
* `TauCeti.exists_norm_mellin_smoothCutoff_le`: uniform-in-`ε` vertical-strip decay of
  `mellin (smoothCutoff ν ε)` for `0 < ε ≤ 1`.
* `TauCeti.verticalIntegrable_mellin_smoothCutoff`: vertical integrability for `C^1` bumps and
  every `ε > 0`.
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

private lemma support_ofReal_comp (ν : ℝ → ℝ) :
    Function.support (fun x ↦ (ν x : ℂ)) = Function.support ν :=
  Function.support_comp_eq (Complex.ofReal : ℝ → ℂ) Complex.ofReal_eq_zero ν

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

/-- Nonnegativity of `deltaSpike` for `ν` nonnegative on `(0, ∞)` and `ε ≥ 0`. -/
theorem deltaSpike_nonneg {ν : ℝ → ℝ} (hν : ∀ x > 0, 0 ≤ ν x) {ε : ℝ} (hε : 0 ≤ ε) (x : ℝ) :
    0 ≤ deltaSpike ν ε x := by
  rw [deltaSpike_def]
  split_ifs with hx
  · exact mul_nonneg (inv_nonneg.mpr hε) (hν _ (Real.rpow_pos_of_pos hx _))
  · exact le_rfl

/-- Multiplicative inversion symmetry of `deltaSpike` when `ν (x⁻¹) = ν x` on `(0, ∞)`. -/
theorem deltaSpike_inv_of_symm {ν : ℝ → ℝ} (hsym : ∀ x, 0 < x → ν x⁻¹ = ν x) (ε : ℝ)
    {x : ℝ} (hx : 0 < x) :
    deltaSpike ν ε x⁻¹ = deltaSpike ν ε x := by
  rw [deltaSpike_of_pos (inv_pos.mpr hx), deltaSpike_of_pos hx, Real.inv_rpow hx.le,
    hsym _ (Real.rpow_pos_of_pos hx _)]

/-- If `Function.support ν ∩ Ioi 0 ⊆ Icc a b` with `0 < a` and `ε > 0`, then `deltaSpike ν ε` is
supported in `[a ^ ε, b ^ ε]`. -/
theorem support_deltaSpike_subset_Icc {ν : ℝ → ℝ} {a b ε : ℝ} (ha : 0 < a) (hε : 0 < ε)
    (hsupp : Function.support ν ∩ Ioi 0 ⊆ Icc a b) :
    Function.support (deltaSpike ν ε) ⊆ Icc (a ^ ε) (b ^ ε) := by
  intro x hx
  have hx0 : 0 < x := by
    by_contra h
    exact hx (deltaSpike_of_nonpos (le_of_not_gt h))
  rw [Function.mem_support, deltaSpike_of_pos hx0] at hx
  have hνx : x ^ ε⁻¹ ∈ Icc a b := hsupp ⟨right_ne_zero_of_mul hx, Real.rpow_pos_of_pos hx0 _⟩
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

/-- For `ν ≥ 0` on `(0, ∞)` with `Function.support ν ∩ Ioi 0 ⊆ Icc a b` (`0 < a`),
`∫₀^∞ ν(x) dx / x = 1`, and `0 < ε ≤ 1`,
`‖mellin (deltaSpike ν ε) 1 - 1‖ ≤ max b 1 * max |log a| |log b| * ε`. -/
theorem norm_mellin_deltaSpike_one_sub_one_le {ν : ℝ → ℝ} {a b ε : ℝ} (ha : 0 < a)
    (hν0 : ∀ x > 0, 0 ≤ ν x) (hνs : Function.support ν ∩ Ioi 0 ⊆ Icc a b)
    (hνm : ∫ x in Ioi (0 : ℝ), ν x / x = 1) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ‖mellin (fun x ↦ (deltaSpike ν ε x : ℂ)) 1 - 1‖ ≤
      max b 1 * max |Real.log a| |Real.log b| * ε := by
  rw [mellin_deltaSpike ν hε0 1, mul_one]
  exact norm_mellin_ofReal_sub_one_le ha hν0 hνs hνm hε0.le hε1

/-! ### Approximate identity for `dx / x` -/

private lemma pos_of_support_inter_Ioi_subset_Icc {ν : ℝ → ℝ} {a b : ℝ}
    (hνs : Function.support ν ∩ Ioi 0 ⊆ Icc a b) (hνm : ∫ x in Ioi (0 : ℝ), ν x / x = 1) :
    0 < b := by
  by_contra hb
  have hzero : ∀ x ∈ Ioi (0 : ℝ), ν x / x = 0 := fun x hx ↦ by
    have hνx : ν x = 0 := Function.notMem_support.mp fun h ↦
      hx.not_ge ((hνs ⟨h, hx⟩).2.trans (not_lt.mp hb))
    simp [hνx]
  rw [setIntegral_eq_zero_of_forall_eq_zero hzero] at hνm
  exact one_ne_zero hνm.symm

private lemma aestronglyMeasurable_comp_exp_neg {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi (0 : ℝ)))) :
    AEStronglyMeasurable (fun v : ℝ ↦ f (Real.exp (-v))) volume := by
  obtain ⟨g, hg, hfg⟩ := hf
  refine ⟨fun v ↦ g (Real.exp (-v)),
    hg.comp_measurable (Real.continuous_exp.measurable.comp measurable_neg), ?_⟩
  let S : Set ℝ := toMeasurable volume ({t : ℝ | f t ≠ g t} ∩ Ioi 0)
  have hS_null : volume S = 0 := by
    rw [measure_toMeasurable]
    have h_ae : ∀ᵐ t : ℝ ∂volume, t ∈ Ioi (0 : ℝ) → f t = g t :=
      (ae_restrict_iff' measurableSet_Ioi).mp hfg
    exact measure_mono_null (s := {t : ℝ | f t ≠ g t} ∩ Ioi 0)
      (t := {t : ℝ | ¬(t ∈ Ioi (0 : ℝ) → f t = g t)})
      (fun t ⟨ht1, ht2⟩ hmem ↦ ht1 (hmem ht2)) (ae_iff.mp h_ae)
  have hS_ae : S.indicator (fun _ : ℝ ↦ (1 : ℝ)) =ᵐ[volume] 0 := by
    have hS_nmem : ∀ᵐ t : ℝ ∂volume, t ∉ S := ae_iff.mpr (by simpa using hS_null)
    filter_upwards [hS_nmem] with t ht
    simp [indicator_of_notMem ht]
  have hS_int :
      Integrable (fun v : ℝ ↦ Real.exp v • S.indicator (fun _ : ℝ ↦ (1 : ℝ)) (Real.exp v)) :=
    (integrable_comp_exp _).mpr (Integrable.congr integrableOn_zero hS_ae.restrict.symm)
  have hS_zero :
      ∫ v : ℝ, Real.exp v • S.indicator (fun _ : ℝ ↦ (1 : ℝ)) (Real.exp v) = 0 := by
    rw [integral_comp_exp]
    exact integral_eq_zero_of_ae hS_ae.restrict
  have hS_nonneg :
      0 ≤ᵐ[volume] fun v : ℝ ↦ Real.exp v • S.indicator (fun _ : ℝ ↦ (1 : ℝ)) (Real.exp v) :=
    Eventually.of_forall fun v ↦
      mul_nonneg (Real.exp_pos v).le (indicator_nonneg (fun _ _ ↦ zero_le_one) _)
  have h_ae_exp : ∀ᵐ v : ℝ ∂volume, f (Real.exp v) = g (Real.exp v) := by
    filter_upwards [(integral_eq_zero_iff_of_nonneg_ae hS_nonneg hS_int).mp hS_zero] with v hv
    by_contra hne
    have hmem : Real.exp v ∈ S := subset_toMeasurable _ _ ⟨hne, Real.exp_pos v⟩
    simp [smul_eq_mul, hmem, (Real.exp_pos v).ne'] at hv
  exact (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae h_ae_exp

private lemma mellinConv_deltaSpike_eq_convolution (ν : ℝ → ℝ) (ε : ℝ) (f : ℝ → ℂ) {x : ℝ}
    (hx : 0 < x) :
    mellinConv (fun y ↦ (deltaSpike ν ε y : ℂ)) f x =
      convolution (fun v : ℝ ↦ deltaSpike ν ε (Real.exp (-v)))
        (fun v : ℝ ↦ f (Real.exp (-v))) (ContinuousLinearMap.lsmul ℝ ℝ) volume (-Real.log x) := by
  have h := ContinuousLinearMap.integral_inv_smul_bilinear_eq_convolution
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ)
    (fun y ↦ deltaSpike ν ε y) f (-Real.log x)
  rw [neg_neg, Real.exp_log hx] at h
  rw [mellinConv_def, ← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ ↦ ?_
  simp only [ContinuousLinearMap.lsmul_apply, Complex.real_smul, ofReal_inv]
  ring

private lemma deltaSpike_log_nonneg {ν : ℝ → ℝ} (hν0 : ∀ x > 0, 0 ≤ ν x) {ε : ℝ}
    (hε : 0 < ε) (v : ℝ) :
    0 ≤ deltaSpike ν ε (Real.exp (-v)) :=
  deltaSpike_nonneg hν0 hε.le (Real.exp (-v))

private lemma deltaSpike_log_integral {ν : ℝ → ℝ} (hνm : ∫ x in Ioi (0 : ℝ), ν x / x = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∫ v : ℝ, deltaSpike ν ε (Real.exp (-v)) = 1 := by
  rw [← integral_neg_eq_self]
  calc
    ∫ v : ℝ, deltaSpike ν ε (Real.exp (- -v))
      = ∫ v : ℝ, Real.exp v • (deltaSpike ν ε (Real.exp v) / Real.exp v) := by
        refine integral_congr_ae (Eventually.of_forall fun v ↦ ?_)
        dsimp only
        rw [neg_neg, smul_eq_mul, mul_div_cancel₀ _ (Real.exp_ne_zero v)]
    _ = ∫ x in Ioi (0 : ℝ), deltaSpike ν ε x / x :=
        integral_comp_exp (fun x ↦ deltaSpike ν ε x / x)
    _ = 1 := (integral_deltaSpike_div ν hε).trans hνm

private lemma support_deltaSpike_log_subset {ν : ℝ → ℝ} {a b ε : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hε : 0 < ε) (hνs : Function.support ν ∩ Ioi 0 ⊆ Icc a b) :
    Function.support (fun v : ℝ ↦ deltaSpike ν ε (Real.exp (-v))) ⊆
      Icc (-ε * Real.log b) (-ε * Real.log a) := by
  intro v hv
  have hmem := support_deltaSpike_subset_Icc ha hε hνs hv
  rw [mem_Icc] at hmem ⊢
  have h1 : Real.log (a ^ ε) ≤ -v := by
    simpa [Real.log_exp] using Real.log_le_log (Real.rpow_pos_of_pos ha ε) hmem.1
  have h2 : -v ≤ Real.log (b ^ ε) := by
    simpa [Real.log_exp] using Real.log_le_log (Real.exp_pos (-v)) hmem.2
  rw [Real.log_rpow ha] at h1
  rw [Real.log_rpow hb] at h2
  exact ⟨by linarith, by linarith⟩

private lemma support_deltaSpike_log_subset_ball {ν : ℝ → ℝ} {a b ε R : ℝ} (ha : 0 < a)
    (hb : 0 < b) (hε : 0 < ε) (hνs : Function.support ν ∩ Ioi 0 ⊆ Icc a b)
    (hR : ε * max |Real.log a| |Real.log b| < R) :
    Function.support (fun v : ℝ ↦ deltaSpike ν ε (Real.exp (-v))) ⊆ Metric.ball (0 : ℝ) R := by
  intro v hv
  have hv_mem := support_deltaSpike_log_subset ha hb hε hνs hv
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
  have hlog : |Real.log a| ≤ max |Real.log a| |Real.log b| := le_max_left _ _
  have hlog' : |Real.log b| ≤ max |Real.log a| |Real.log b| := le_max_right _ _
  have h1 : -(ε * max |Real.log a| |Real.log b|) ≤ -ε * Real.log b := by
    nlinarith [neg_abs_le (Real.log b), le_abs_self (Real.log b)]
  have h2 : -ε * Real.log a ≤ ε * max |Real.log a| |Real.log b| := by
    nlinarith [neg_abs_le (Real.log a), le_abs_self (Real.log a)]
  exact ⟨lt_of_lt_of_le (neg_lt_neg hR) (h1.trans hv_mem.1),
    lt_of_le_of_lt (hv_mem.2.trans h2) hR⟩

/-- Quantitative approximate-identity bound: if `ν ≥ 0` on `(0, ∞)` has
`Function.support ν ∩ Ioi 0 ⊆ Icc a b` (`0 < a`) and `∫₀^∞ ν(x) dx / x = 1`, `f : ℝ → ℂ` is
`AEStronglyMeasurable` on `(0, ∞)`, `ε > 0`, `x > 0`, and `‖f (x / y) - f x‖ ≤ M` for all
`y ∈ [a ^ ε, b ^ ε]`, then `‖mellinConv (deltaSpike ν ε) f x - f x‖ ≤ M`. -/
theorem norm_mellinConv_deltaSpike_sub_le {ν : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hν0 : ∀ x > 0, 0 ≤ ν x) (hνs : Function.support ν ∩ Ioi 0 ⊆ Icc a b)
    (hνm : ∫ x in Ioi (0 : ℝ), ν x / x = 1)
    {f : ℝ → ℂ} (hf : AEStronglyMeasurable f (volume.restrict (Ioi (0 : ℝ))))
    {ε x M : ℝ} (hε : 0 < ε) (hx : 0 < x)
    (hbd : ∀ y ∈ Icc (a ^ ε) (b ^ ε), ‖f (x / y) - f x‖ ≤ M) :
    ‖mellinConv (fun y ↦ (deltaSpike ν ε y : ℂ)) f x - f x‖ ≤ M := by
  have hb : 0 < b := pos_of_support_inter_Ioi_subset_Icc hνs hνm
  let φ : ℝ → ℝ := fun v ↦ deltaSpike ν ε (Real.exp (-v))
  let g : ℝ → ℂ := fun v ↦ f (Real.exp (-v))
  let u : ℝ := -Real.log x
  let s : Set ℝ := Icc (-ε * Real.log b) (-ε * Real.log a)
  have hφ_int : Integrable φ volume :=
    integrable_of_integral_eq_one (deltaSpike_log_integral hνm hε)
  have hφ_supp : Function.support φ ⊆ s := support_deltaSpike_log_subset ha hb hε hνs
  have hexp_mem {v : ℝ} (hv : v ∈ s) : Real.exp (-v) ∈ Icc (a ^ ε) (b ^ ε) := by
    have h1 : ε * Real.log a ≤ -v := by linarith [hv.2]
    have h2 : -v ≤ ε * Real.log b := by linarith [hv.1]
    rw [← Real.log_rpow ha] at h1
    rw [← Real.log_rpow hb] at h2
    exact ⟨by simpa [Real.exp_log (Real.rpow_pos_of_pos ha ε)] using Real.exp_le_exp.mpr h1,
      by simpa [Real.exp_log (Real.rpow_pos_of_pos hb ε)] using Real.exp_le_exp.mpr h2⟩
  have hdiv_eq (v : ℝ) : Real.exp (-(u - v)) = x / Real.exp (-v) := by
    rw [show x = Real.exp (Real.log x) from (Real.exp_log hx).symm, ← Real.exp_sub]
    congr 1
    simp [u]
    ring
  have hconv_ex : ConvolutionExistsAt φ g u (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    refine BddAbove.convolutionExistsAt (s := s) (ContinuousLinearMap.lsmul ℝ ℝ) ?_
      measurableSet_Icc ?_ (hφ_int.integrableOn (s := s)) (aestronglyMeasurable_comp_exp_neg hf)
    · refine ⟨‖f x‖ + M, ?_⟩
      rintro _ ⟨w, hw, rfl⟩
      have hy : Real.exp (-(u - w)) ∈ Icc (a ^ ε) (b ^ ε) := hexp_mem hw
      have hsub : Real.exp (-w) = x / Real.exp (-(u - w)) := by
        conv_lhs => rw [show w = u - (u - w) from (sub_sub_cancel u w).symm, hdiv_eq (u - w)]
      rw [show (fun i ↦ ‖g i‖) w = ‖f (Real.exp (-w))‖ from rfl, hsub]
      exact norm_le_norm_add_const_of_dist_le (by simpa [dist_eq_norm] using hbd _ hy)
    · intro v hv
      exact hφ_supp fun h ↦ hv (by simp [h])
  have hint_const : Integrable (fun v : ℝ ↦ φ v • f x) volume := hφ_int.smul_const (f x)
  have hint_diff : Integrable (fun v : ℝ ↦ φ v • (g (u - v) - f x)) volume := by
    convert hconv_ex.integrable.sub hint_const using 1
    ext v
    simp [smul_sub, ContinuousLinearMap.lsmul_apply]
  have hsub_eq : mellinConv (fun y ↦ (deltaSpike ν ε y : ℂ)) f x - f x =
      ∫ v : ℝ, φ v • (g (u - v) - f x) := by
    rw [mellinConv_deltaSpike_eq_convolution ν ε f hx, convolution_def]
    have hfx : f x = ∫ v : ℝ, φ v • f x := by
      rw [integral_smul_const, deltaSpike_log_integral hνm hε, one_smul]
    conv_lhs => rhs; rw [hfx]
    rw [← integral_sub hconv_ex.integrable hint_const]
    refine integral_congr_ae (Eventually.of_forall fun v ↦ ?_)
    simp [smul_sub, ContinuousLinearMap.lsmul_apply]
  rw [hsub_eq]
  have hM_nn : 0 ≤ M := by
    have hne : (Icc (a ^ ε) (b ^ ε)).Nonempty :=
      ⟨a ^ ε, le_rfl, Real.rpow_le_rpow ha.le (by
        by_contra h
        have hlt : b < a := not_le.mp h
        have hzero : ∀ z ∈ Ioi (0 : ℝ), ν z / z = 0 := fun z hz ↦ by
          have : ν z = 0 := Function.notMem_support.mp fun hsup ↦
            hlt.not_ge ((hνs ⟨hsup, hz⟩).1.trans (hνs ⟨hsup, hz⟩).2)
          simp [this]
        rw [setIntegral_eq_zero_of_forall_eq_zero hzero] at hνm
        exact one_ne_zero hνm.symm) hε.le⟩
    obtain ⟨y, hy⟩ := hne
    exact (norm_nonneg _).trans (hbd y hy)
  calc
    ‖∫ v : ℝ, φ v • (g (u - v) - f x)‖
      ≤ ∫ v : ℝ, ‖φ v • (g (u - v) - f x)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ v : ℝ, M * φ v := by
        refine integral_mono hint_diff.norm (hφ_int.const_mul M) fun v ↦ ?_
        rw [norm_smul, Real.norm_of_nonneg (deltaSpike_log_nonneg hν0 hε v)]
        by_cases hφv : φ v = 0
        · have h0 : deltaSpike ν ε (Real.exp (-v)) = 0 := hφv
          rw [h0, zero_mul]
          exact mul_nonneg hM_nn (deltaSpike_log_nonneg hν0 hε v)
        · rw [mul_comm M]
          refine mul_le_mul_of_nonneg_left ?_ (deltaSpike_log_nonneg hν0 hε v)
          have hy : Real.exp (-v) ∈ Icc (a ^ ε) (b ^ ε) := hexp_mem (hφ_supp hφv)
          have harg : Real.exp (v - u) = x / Real.exp (-v) := by
            simpa [neg_sub] using hdiv_eq v
          simpa [g, harg] using hbd (Real.exp (-v)) hy
    _ = M := by rw [integral_const_mul, deltaSpike_log_integral hνm hε, mul_one]

/-- Pointwise approximate identity for `dx / x`: if `ν ≥ 0` on `(0, ∞)` has
`Function.support ν ∩ Ioi 0 ⊆ Icc a b` (`0 < a`) with `∫₀^∞ ν(x) dx / x = 1`, and
`f : ℝ → ℂ` is `AEStronglyMeasurable` on `(0, ∞)` and continuous at `x > 0`, then
`mellinConv (deltaSpike ν ε) f x → f x` as `ε → 0⁺`. -/
theorem tendsto_mellinConv_deltaSpike {ν : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hν0 : ∀ x > 0, 0 ≤ ν x) (hνs : Function.support ν ∩ Ioi 0 ⊆ Icc a b)
    (hνm : ∫ x in Ioi (0 : ℝ), ν x / x = 1)
    {f : ℝ → ℂ} (hf : AEStronglyMeasurable f (volume.restrict (Ioi (0 : ℝ))))
    {x : ℝ} (hx : 0 < x) (hcont : ContinuousAt f x) :
    Tendsto (fun ε : ℝ ↦ mellinConv (fun y ↦ (deltaSpike ν ε y : ℂ)) f x) (𝓝[>] 0) (𝓝 (f x)) := by
  have hb : 0 < b := pos_of_support_inter_Ioi_subset_Icc hνs hνm
  have htend := MeasureTheory.convolution_tendsto_right
    (l := 𝓝[>] (0 : ℝ)) (μ := volume)
    (φ := fun ε v ↦ deltaSpike ν ε (Real.exp (-v)))
    (g := fun _ v ↦ f (Real.exp (-v)))
    (k := fun _ ↦ -Real.log x)
    (x₀ := -Real.log x) (z₀ := f x)
    (by
      filter_upwards [self_mem_nhdsWithin] with ε hε v
      exact deltaSpike_log_nonneg hν0 hε v)
    (by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact deltaSpike_log_integral hνm hε)
    (by
      rw [tendsto_smallSets_iff]
      intro s hs
      obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp hs
      let L := max |Real.log a| |Real.log b| + 1
      filter_upwards [Ioo_mem_nhdsGT (div_pos hR (by positivity : 0 < L))] with ε hε
      refine (support_deltaSpike_log_subset_ball ha hb hε.1 hνs ?_).trans hball
      have hεL : ε * max |Real.log a| |Real.log b| < ε * L := by
        gcongr
        · exact hε.1
        · exact lt_add_one _
      exact hεL.trans ((lt_div_iff₀ (by positivity : 0 < L)).mp hε.2))
    (Eventually.of_forall fun _ ↦ aestronglyMeasurable_comp_exp_neg hf)
    (by
      have hc : Tendsto (fun v : ℝ ↦ f (Real.exp (-v))) (𝓝 (-Real.log x)) (𝓝 (f x)) := by
        refine hcont.tendsto.comp ?_
        have hcomp : ContinuousAt (fun v : ℝ ↦ Real.exp (-v)) (-Real.log x) :=
          Real.continuous_exp.continuousAt.comp continuousAt_neg
        simpa [Real.exp_log hx] using hcomp.tendsto
      exact hc.comp tendsto_snd)
    tendsto_const_nhds
  refine htend.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε _
  exact (mellinConv_deltaSpike_eq_convolution ν ε f hx).symm

/-- Uniform approximate identity on compact subsets of `(0, ∞)`: if `ν ≥ 0` on `(0, ∞)` has
`Function.support ν ∩ Ioi 0 ⊆ Icc a b` (`0 < a`) with `∫₀^∞ ν(x) dx / x = 1`, `f : ℝ → ℂ` is
continuous on `(0, ∞)`, and `K ⊆ (0, ∞)` is compact, then `mellinConv (deltaSpike ν ε) f → f`
uniformly on `K` as `ε → 0⁺`. -/
theorem tendstoUniformlyOn_mellinConv_deltaSpike {ν : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hν0 : ∀ x > 0, 0 ≤ ν x) (hνs : Function.support ν ∩ Ioi 0 ⊆ Icc a b)
    (hνm : ∫ x in Ioi (0 : ℝ), ν x / x = 1)
    {f : ℝ → ℂ} (hf : ContinuousOn f (Ioi (0 : ℝ))) {K : Set ℝ} (hK : IsCompact K)
    (hK_sub : K ⊆ Ioi (0 : ℝ)) :
    TendstoUniformlyOn (fun ε x ↦ mellinConv (fun y ↦ (deltaSpike ν ε y : ℂ)) f x) f
      (𝓝[>] 0) K := by
  have hb : 0 < b := pos_of_support_inter_Ioi_subset_Icc hνs hνm
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact Eventually.of_forall fun _ _ h ↦ False.elim h
  obtain ⟨c, hcK, hc_min⟩ := hK.exists_isMinOn hKne continuousOn_id
  obtain ⟨d, _hdK, hd_max⟩ := hK.exists_isMaxOn hKne continuousOn_id
  have hc : 0 < c := hK_sub hcK
  let g : ℝ → ℂ := fun v ↦ f (Real.exp (-v))
  have hg_cont : Continuous g := continuousOn_univ.mp
    (hf.comp (Real.continuous_exp.comp continuous_neg).continuousOn fun v _ ↦ Real.exp_pos (-v))
  let L_log : Set ℝ := Icc (-Real.log d - 1) (-Real.log c + 1)
  have hunif : UniformContinuousOn g L_log := isCompact_Icc.uniformContinuousOn_of_continuous
    hg_cont.continuousOn
  obtain ⟨δ, hδ, hδ_unif⟩ := Metric.uniformContinuousOn_iff.mp hunif (η / 2) (half_pos hη)
  let R := min δ 1
  have hR : 0 < R := lt_min hδ zero_lt_one
  let M_log := max |Real.log a| |Real.log b| + 1
  filter_upwards [Ioo_mem_nhdsGT (div_pos hR (by positivity : 0 < M_log))] with ε hε x hxK
  have hx0 : 0 < x := hK_sub hxK
  have hsupp_ball : Function.support (fun v : ℝ ↦ deltaSpike ν ε (Real.exp (-v))) ⊆
      Metric.ball (0 : ℝ) R := by
    refine support_deltaSpike_log_subset_ball ha hb hε.1 hνs ?_
    have h1 : ε * max |Real.log a| |Real.log b| < ε * M_log := by
      gcongr
      · exact hε.1
      · exact lt_add_one _
    exact h1.trans ((lt_div_iff₀ (by positivity : 0 < M_log)).mp hε.2)
  have hu_mem : -Real.log x ∈ Icc (-Real.log d) (-Real.log c) :=
    ⟨neg_le_neg (Real.log_le_log hx0 (hd_max hxK)),
      neg_le_neg (Real.log_le_log hc (hc_min hxK))⟩
  have hdist := MeasureTheory.dist_convolution_le (μ := volume) (x₀ := -Real.log x) (R := R)
    (ε := η / 2) (z₀ := f x) (half_pos hη).le hsupp_ball
    (deltaSpike_log_nonneg hν0 hε.1) (deltaSpike_log_integral hνm hε.1)
    hg_cont.aestronglyMeasurable fun v hv ↦ by
      rw [Metric.mem_ball, Real.dist_eq] at hv
      have hvL : v ∈ L_log := ⟨by linarith [abs_lt.mp hv, hu_mem.1, min_le_right δ 1],
        by linarith [abs_lt.mp hv, hu_mem.2, min_le_right δ 1]⟩
      have huL : -Real.log x ∈ L_log := ⟨by linarith [hu_mem.1], by linarith [hu_mem.2]⟩
      have hv_lt : dist v (-Real.log x) < δ :=
        (Real.dist_eq v (-Real.log x) ▸ hv).trans_le (min_le_left δ 1)
      have hval : g (-Real.log x) = f x := by simp [g, Real.exp_log hx0]
      exact hval ▸ (hδ_unif v hvL (-Real.log x) huL hv_lt).le
  rw [← mellinConv_deltaSpike_eq_convolution ν ε f hx0, dist_comm] at hdist
  exact hdist.trans_lt (half_lt_self hη)

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
  rw [mellinConv_comm_of_pos _ _ hx, mellinConv_def, smoothCutoff_of_pos hx,
    ← integral_complex_ofReal]
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

/-- Nonnegativity of `smoothCutoff` for `ν` nonnegative on `(0, ∞)` and `ε ≥ 0`. -/
theorem smoothCutoff_nonneg {ν : ℝ → ℝ} (hν0 : ∀ x > 0, 0 ≤ ν x) {ε : ℝ} (hε : 0 ≤ ε) (x : ℝ) :
    0 ≤ smoothCutoff ν ε x := by
  rw [smoothCutoff_def]
  split_ifs with hx
  · exact setIntegral_nonneg measurableSet_Ioi fun z hz ↦
      div_nonneg (deltaSpike_nonneg hν0 hε z) (hx.trans hz).le
  · exact le_rfl

/-- Upper bound `smoothCutoff ν ε x ≤ 1` for `ν` nonnegative on `(0, ∞)` with `dx / x`-mass `1`
and `ε > 0`. -/
theorem smoothCutoff_le_one {ν : ℝ → ℝ} (hν0 : ∀ x > 0, 0 ≤ ν x)
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

/-- `smoothCutoff ν ε` is antitone on `(0, ∞)` whenever `ε > 0`, `ν ≥ 0` on `(0, ∞)`, and
`ν x / x` is integrable on `(0, ∞)`. -/
theorem smoothCutoff_antitoneOn {ν : ℝ → ℝ} (hν0 : ∀ x > 0, 0 ≤ ν x)
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

/-- Plateau at `1`: for `ε > 0` and `ν` with `Function.support ν ∩ Ioi 0 ⊆ Ici a` (`0 < a`) and
`dx / x`-mass `1`, `smoothCutoff ν ε x = 1` for all `0 < x ≤ a ^ ε`. -/
theorem smoothCutoff_eq_one {ν : ℝ → ℝ} {a ε x : ℝ} (ha : 0 < a)
    (hνs : Function.support ν ∩ Ioi 0 ⊆ Ici a) (hνm : ∫ x in Ioi (0 : ℝ), ν x / x = 1)
    (hε : 0 < ε) (hx0 : 0 < x) (hx : x ≤ a ^ ε) :
    smoothCutoff ν ε x = 1 := by
  rw [smoothCutoff_of_pos hx0]
  have heq : (∫ z in Ioi x, deltaSpike ν ε z / z) = ∫ z in Ioi (0 : ℝ), deltaSpike ν ε z / z := by
    refine (setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Ioi.nullMeasurableSet
      (Ioi_subset_Ioi hx0.le) ?_).symm
    have hae_ne : ∀ᵐ z : ℝ ∂volume, z ≠ x := by rw [ae_iff]; simp
    filter_upwards [hae_ne] with z hzx hzdiff
    have hz0 : 0 < z := hzdiff.1
    have hlt : z < x := lt_of_le_of_ne (le_of_not_gt hzdiff.2) hzx
    have hpow_lt : z ^ ε⁻¹ < a := by
      have h1 : z ^ ε⁻¹ < (a ^ ε) ^ ε⁻¹ :=
        Real.rpow_lt_rpow hz0.le (hlt.trans_le hx) (inv_pos.mpr hε)
      rwa [← Real.rpow_mul ha.le, mul_inv_cancel₀ hε.ne', Real.rpow_one] at h1
    have hνz : ν (z ^ ε⁻¹) = 0 := Function.notMem_support.mp fun h ↦
      hpow_lt.not_ge (hνs ⟨h, Real.rpow_pos_of_pos hz0 _⟩)
    simp [deltaSpike_of_pos hz0, hνz]
  rw [heq, integral_deltaSpike_div ν hε, hνm]

/-- Plateau at `0`: for `ε > 0` and `ν` with `Function.support ν ∩ Ioi 0 ⊆ Iic b`,
`smoothCutoff ν ε x = 0` for all `b ^ ε ≤ x`. -/
theorem smoothCutoff_eq_zero_of_le {ν : ℝ → ℝ} {b ε x : ℝ}
    (hνs : Function.support ν ∩ Ioi 0 ⊆ Iic b) (hε : 0 < ε) (hx : b ^ ε ≤ x) :
    smoothCutoff ν ε x = 0 := by
  by_cases hx0 : 0 < x
  · rw [smoothCutoff_of_pos hx0]
    refine setIntegral_eq_zero_of_forall_eq_zero fun z hz ↦ ?_
    have hz0 : 0 < z := hx0.trans hz
    have hpow_gt : b < z ^ ε⁻¹ := by
      rcases le_or_gt b 0 with hb | hb
      · exact hb.trans_lt (Real.rpow_pos_of_pos hz0 _)
      · have h1 : (b ^ ε) ^ ε⁻¹ < z ^ ε⁻¹ :=
          Real.rpow_lt_rpow (Real.rpow_pos_of_pos hb ε).le (hx.trans_lt hz) (inv_pos.mpr hε)
        rwa [← Real.rpow_mul hb.le, mul_inv_cancel₀ hε.ne', Real.rpow_one] at h1
    have hνz : ν (z ^ ε⁻¹) = 0 := Function.notMem_support.mp fun h ↦
      hpow_gt.not_ge (hνs ⟨h, Real.rpow_pos_of_pos hz0 _⟩)
    simp [deltaSpike_of_pos hz0, hνz]
  · exact smoothCutoff_of_nonpos (le_of_not_gt hx0)

/-- For `ε > 0` and a multiplicatively symmetric bump (`ν x⁻¹ = ν x` on `(0, ∞)`) of
`dx / x`-mass `1`, `smoothCutoff ν ε 1 = 1 / 2`. -/
theorem smoothCutoff_one_of_symm {ν : ℝ → ℝ} (hsym : ∀ x, 0 < x → ν x⁻¹ = ν x)
    (hνm : ∫ x in Ioi (0 : ℝ), ν x / x = 1) {ε : ℝ} (hε : 0 < ε) :
    smoothCutoff ν ε 1 = 1 / 2 := by
  have hint : IntegrableOn (fun z ↦ deltaSpike ν ε z / z) (Ioi (0 : ℝ)) :=
    (integrableOn_deltaSpike_div_iff hε).mpr (integrable_of_integral_eq_one hνm)
  have hsplit := intervalIntegral.integral_interval_add_Ioi hint
    (hint.mono_set (Ioi_subset_Ioi zero_le_one))
  rw [intervalIntegral.integral_of_le zero_le_one] at hsplit
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
  exact (hint.continuousOn_Ici_primitive_Ioi.mono Ioi_subset_Ici_self).congr
    fun _ hx ↦ smoothCutoff_of_pos hx

/-- For `ε > 0`, `Re s > 0`, and `MellinConvergent ν (ε * s)`, the smoothed cutoff
`smoothCutoff ν ε` has absolutely convergent Mellin transform `mellin ν (ε * s) / s`. -/
theorem hasMellin_smoothCutoff {ν : ℝ → ℝ} {ε : ℝ} {s : ℂ} (hε : 0 < ε) (hs : 0 < s.re)
    (hν : MellinConvergent (fun x ↦ (ν x : ℂ)) (ε * s)) :
    HasMellin (fun x ↦ (smoothCutoff ν ε x : ℂ)) s
      (mellin (fun x ↦ (ν x : ℂ)) (ε * s) / s) := by
  have h1 : HasMellin ((Ioc (0 : ℝ) 1).indicator (1 : ℝ → ℂ)) s (1 / s) := hasMellin_one_Ioc hs
  have h2 : MellinConvergent (fun x ↦ (deltaSpike ν ε x : ℂ)) s :=
    (mellinConvergent_deltaSpike_iff hε s).mpr hν
  have hconv := hasMellin_mellinConv h1.1 h2
  rw [h1.2, mellin_deltaSpike ν hε s, one_div_mul_eq_div] at hconv
  exact (TauCeti.hasMellin_congr fun _ hx ↦ smoothCutoff_eq_mellinConv ν ε hx).mpr hconv

/-- Mellin transform of the smoothed cutoff: for `ε > 0`, `Re s > 0`, and
`MellinConvergent ν (ε * s)`, `mellin (smoothCutoff ν ε) s = mellin ν (ε * s) / s`. -/
theorem mellin_smoothCutoff {ν : ℝ → ℝ} {ε : ℝ} {s : ℂ} (hε : 0 < ε) (hs : 0 < s.re)
    (hν : MellinConvergent (fun x ↦ (ν x : ℂ)) (ε * s)) :
    mellin (fun x ↦ (smoothCutoff ν ε x : ℂ)) s = mellin (fun x ↦ (ν x : ℂ)) (ε * s) / s :=
  (hasMellin_smoothCutoff hε hs hν).2

private lemma exists_norm_mellin_smoothCutoff_le_of_le {ν : ℝ → ℝ} {a b E σ₂ : ℝ} {k : ℕ}
    (ha : 0 < a) (hsupp : Function.support ν ∩ Ioi 0 ⊆ Icc a b)
    (hν : ContDiffOn ℝ k ν (Ioi (0 : ℝ))) (hE : 0 < E) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ E → ∀ s : ℂ, 0 < s.re → s.re ≤ σ₂ →
      ‖mellin (fun x ↦ (smoothCutoff ν ε x : ℂ)) s‖ ≤ C / (‖s‖ * (1 + ε * ‖s‖) ^ k) := by
  have hνc : ContDiffOn ℝ k (fun x ↦ (ν x : ℂ)) (Ioi (0 : ℝ)) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hν
  have hsuppc : Function.support (fun x ↦ (ν x : ℂ)) ∩ Ioi 0 ⊆ Icc a b := by
    rwa [support_ofReal_comp]
  have hloc : LocallyIntegrableOn (fun x ↦ (ν x : ℂ)) (Ioi (0 : ℝ)) :=
    hνc.continuousOn.locallyIntegrableOn measurableSet_Ioi
  obtain ⟨C, hC0, hC⟩ := exists_norm_mellin_le_of_contDiffOn_of_support_subset_Icc
    (σ₁ := 0) (σ₂ := max (E * σ₂) 0) ha hsuppc hνc
  refine ⟨C, hC0, fun ε hε0 hεE s hs0 hs₂ ↦ ?_⟩
  have hεs_re₁ : 0 ≤ ((ε : ℂ) * s).re := by
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg hε0.le hs0.le
  have hεs_re₂ : ((ε : ℂ) * s).re ≤ max (E * σ₂) 0 := by
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    exact (mul_le_mul hεE hs₂ hs0.le hE.le).trans (le_max_left _ _)
  have hbd := hC ((ε : ℂ) * s) hεs_re₁ hεs_re₂
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε0] at hbd
  rw [mellin_smoothCutoff hε0 hs0
    (mellinConvergent_of_support_subset_Icc ha hsuppc hloc ((ε : ℂ) * s)), norm_div,
    div_mul_eq_div_div, div_right_comm]
  exact div_le_div_of_nonneg_right hbd (norm_nonneg s)

/-- Uniform-in-`ε` vertical-strip decay of the Mellin transform of `smoothCutoff ν ε`: if `ν` is
`C^k` on `(0, ∞)` with `Function.support ν ∩ Ioi 0 ⊆ Icc a b` (`0 < a`), then for every `σ₂`
there exists `C ≥ 0` such that `‖mellin (smoothCutoff ν ε) s‖ ≤ C / (‖s‖ * (1 + ε * ‖s‖) ^ k)`
for all `0 < ε ≤ 1` and `0 < Re s ≤ σ₂`. -/
theorem exists_norm_mellin_smoothCutoff_le {ν : ℝ → ℝ} {a b σ₂ : ℝ} {k : ℕ} (ha : 0 < a)
    (hsupp : Function.support ν ∩ Ioi 0 ⊆ Icc a b) (hν : ContDiffOn ℝ k ν (Ioi (0 : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ s : ℂ, 0 < s.re → s.re ≤ σ₂ →
      ‖mellin (fun x ↦ (smoothCutoff ν ε x : ℂ)) s‖ ≤ C / (‖s‖ * (1 + ε * ‖s‖) ^ k) :=
  exists_norm_mellin_smoothCutoff_le_of_le ha hsupp hν zero_lt_one

/-- Vertical integrability of `mellin (smoothCutoff ν ε)` on `Re s = σ > 0` for any `C^1` bump
`ν` on `(0, ∞)` with `Function.support ν ∩ Ioi 0 ⊆ Icc a b` (`0 < a`) and any `ε > 0`. -/
theorem verticalIntegrable_mellin_smoothCutoff {ν : ℝ → ℝ} {a b ε σ : ℝ} (ha : 0 < a)
    (hsupp : Function.support ν ∩ Ioi 0 ⊆ Icc a b) (hν : ContDiffOn ℝ 1 ν (Ioi (0 : ℝ)))
    (hε : 0 < ε) (hσ : 0 < σ) :
    VerticalIntegrable (mellin (fun x ↦ (smoothCutoff ν ε x : ℂ))) σ := by
  have hνc : ContDiffOn ℝ 1 (fun x ↦ (ν x : ℂ)) (Ioi (0 : ℝ)) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hν
  have hsuppc : Function.support (fun x ↦ (ν x : ℂ)) ∩ Ioi 0 ⊆ Icc a b := by
    rwa [support_ofReal_comp]
  have hloc : LocallyIntegrableOn (fun x ↦ (ν x : ℂ)) (Ioi (0 : ℝ)) :=
    hνc.continuousOn.locallyIntegrableOn measurableSet_Ioi
  obtain ⟨C, hC0, hC⟩ := exists_norm_mellin_smoothCutoff_le_of_le (E := ε) (σ₂ := σ) ha hsupp hν hε
  have hcont : Continuous fun t : ℝ ↦
      mellin (fun x ↦ (smoothCutoff ν ε x : ℂ)) ((σ : ℂ) + t * I) := by
    have hline : ∀ t : ℝ, mellin (fun x ↦ (smoothCutoff ν ε x : ℂ)) ((σ : ℂ) + t * I) =
        mellin (fun x ↦ (ν x : ℂ)) ((ε : ℂ) * ((σ : ℂ) + t * I)) / ((σ : ℂ) + t * I) := fun t ↦
      mellin_smoothCutoff hε (by simp [hσ])
        (mellinConvergent_of_support_subset_Icc ha hsuppc hloc _)
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
  have hbd := hC ε hε le_rfl s (by simp [s, hσ]) (by simp [s])
  rw [pow_one] at hbd
  have hre : σ ≤ ‖s‖ := by simpa [s, abs_of_pos hσ] using Complex.abs_re_le_norm s
  have him : |t| ≤ ‖s‖ := by simpa [s] using Complex.abs_im_le_norm s
  have hsq : t ^ 2 ≤ ‖s‖ ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg t) him 2
  have hdenom : min σ ε * (1 + t ^ 2) ≤ ‖s‖ * (1 + ε * ‖s‖) := by
    have h1 : min σ ε ≤ ‖s‖ := (min_le_left σ ε).trans hre
    have h2 : min σ ε * t ^ 2 ≤ ε * ‖s‖ ^ 2 :=
      mul_le_mul (min_le_right σ ε) hsq (sq_nonneg t) hε.le
    nlinarith
  calc
    ‖mellin (fun x ↦ (smoothCutoff ν ε x : ℂ)) s‖
      ≤ C / (‖s‖ * (1 + ε * ‖s‖)) := hbd
    _ ≤ C / (min σ ε * (1 + t ^ 2)) :=
        div_le_div_of_nonneg_left hC0 (mul_pos hm_pos (by positivity)) hdenom
    _ = C / min σ ε * (1 + t ^ 2)⁻¹ := by rw [div_mul_eq_div_div, div_eq_mul_inv]

/-- For `ν ≥ 0` on `(0, ∞)` with `Function.support ν ∩ Ioi 0 ⊆ Icc a b` (`0 < a`),
`∫₀^∞ ν(x) dx / x = 1`, and `0 < ε ≤ 1`,
`‖mellin (smoothCutoff ν ε) 1 - 1‖ ≤ max b 1 * max |log a| |log b| * ε`. -/
theorem norm_mellin_smoothCutoff_one_sub_one_le {ν : ℝ → ℝ} {a b ε : ℝ} (ha : 0 < a)
    (hν0 : ∀ x > 0, 0 ≤ ν x) (hνs : Function.support ν ∩ Ioi 0 ⊆ Icc a b)
    (hνm : ∫ x in Ioi (0 : ℝ), ν x / x = 1) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ‖mellin (fun x ↦ (smoothCutoff ν ε x : ℂ)) 1 - 1‖ ≤
      max b 1 * max |Real.log a| |Real.log b| * ε := by
  have hconv0 : MellinConvergent (fun x ↦ (ν x : ℂ)) 0 :=
    (mellinConvergent_ofReal_zero_iff ν).mpr (integrable_of_integral_eq_one hνm)
  have hsuppc : Function.support (fun x ↦ (ν x : ℂ)) ∩ Ioi 0 ⊆ Icc a b := by
    rwa [support_ofReal_comp]
  have hconv : MellinConvergent (fun x ↦ (ν x : ℂ)) ((ε : ℂ) * 1) :=
    hconv0.of_support_subset_Icc ha hsuppc ((ε : ℂ) * 1)
  rw [mellin_smoothCutoff hε0 (by simp) hconv, mul_one, div_one]
  exact norm_mellin_ofReal_sub_one_le ha hν0 hνs hνm hε0.le hε1

/-! ### Existence of a symmetric smooth bump -/

/-- For every `R > 1`, there exists a `C^∞`, nonnegative, multiplicatively symmetric bump function
`ν : ℝ → ℝ` supported in `[R⁻¹, R]` with `∫₀^∞ ν(x) dx / x = 1`, constructed by pulling back
Mathlib's normalized bump `ContDiffBump.normed` along `Real.log` on `(0, ∞)` (and extending by `0`
on `(-∞, 0]`). -/
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
