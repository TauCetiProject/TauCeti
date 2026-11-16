/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import TauCeti.Analysis.MellinTransform.Convolution
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Analysis.MellinTransform
import TauCeti.Analysis.MellinTransform.CompactSupport

/-!
# Multiplicative delta spikes and smoothed cutoffs

Given a bump `ν : ℝ → ℝ` and scale `ε > 0`, the multiplicative delta spike is
`deltaSpike ν ε x = ε⁻¹ * ν (x ^ ε⁻¹)` for `x > 0` and `0` for `x ≤ 0`. It preserves the
multiplicative mass `∫₀^∞ ν(x) dx/x`, compresses support `[a, b]` to `[a ^ ε, b ^ ε]`, has Mellin
transform `s ↦ mellin ν (ε * s)`, and forms an approximate identity for `mellinConv` as `ε → 0⁺`,
both pointwise at points of continuity and uniformly on compact subsets of `(0, ∞)`.

Convolving the sharp cutoff `1_(0,1]` with `deltaSpike ν ε` gives the smoothed cutoff
`smoothCutoff ν ε x = ∫_{(x,∞)} deltaSpike ν ε z dz/z` for `x > 0` and `0` for `x ≤ 0`. On
`Re s > 0` its Mellin transform is `mellin ν (ε * s) / s`, which decays uniformly in `ε ∈ (0, 1]`
like `O(1 / (‖s‖ * (1 + ε * ‖s‖) ^ k))` on every half-strip `0 < Re s ≤ σ₂` when `ν` is `C^k`
and compactly supported in `(0, ∞)`. In particular, for `k ≥ 1` the transform is integrable on
every positive vertical line `Re s = σ > 0`.

## Main results

* `TauCeti.deltaSpike`: the multiplicative delta spike `ε⁻¹ * ν (x ^ ε⁻¹)` on `(0, ∞)`.
* `TauCeti.support_deltaSpike_subset`, `TauCeti.integral_deltaSpike_div`,
  `TauCeti.mellin_deltaSpike`, `TauCeti.norm_mellin_sub_one_le`: support, `dx/x`-mass, Mellin
  transform, and linear perturbation bound for `deltaSpike`.
* `TauCeti.tendsto_mellinConv_deltaSpike` and `TauCeti.tendstoUniformlyOn_mellinConv_deltaSpike`:
  pointwise and compact-uniform approximate identity for `mellinConv`.
* `TauCeti.smoothCutoff`: the smoothed cutoff `∫_{(x,∞)} deltaSpike ν ε z dz/z` on `(0, ∞)`.
* `TauCeti.smoothCutoff_eq_mellinConv`, `TauCeti.smoothCutoff_eq_one_of_le`,
  `TauCeti.smoothCutoff_eq_zero_of_le`, `TauCeti.continuousOn_smoothCutoff`: basic cutoff
  properties and regularity on `(0, ∞)`.
* `TauCeti.hasMellin_smoothCutoff` and `TauCeti.mellin_smoothCutoff`: Mellin transform
  `mellin ν (ε * s) / s` for `0 < Re s`.
* `TauCeti.norm_mellin_smoothCutoff_le` and `TauCeti.verticalIntegrable_mellin_smoothCutoff`:
  `ε`-uniform vertical-strip decay and vertical-line integrability.

## References

* Alex Kontorovich, Terence Tao, et al., *Prime Number Theorem And …*, §4.3 (delta spikes and
  smoothed cutoffs).
-/

public section

open MeasureTheory Complex Set Filter
open scoped Topology

namespace TauCeti

/-! ### Multiplicative delta spikes -/

/-- The multiplicative delta spike associated to a bump `ν : ℝ → ℝ` at scale `ε`:
`ε⁻¹ * ν (x ^ ε⁻¹)` for `x > 0`, and `0` for `x ≤ 0`. -/
noncomputable def deltaSpike (ν : ℝ → ℝ) (ε x : ℝ) : ℝ :=
  if 0 < x then ε⁻¹ * ν (x ^ ε⁻¹) else 0

/-- Unfolding lemma for `deltaSpike`. -/
theorem deltaSpike_def (ν : ℝ → ℝ) (ε x : ℝ) :
    deltaSpike ν ε x = if 0 < x then ε⁻¹ * ν (x ^ ε⁻¹) else 0 := (rfl)

@[simp]
theorem deltaSpike_of_pos (ν : ℝ → ℝ) (ε : ℝ) {x : ℝ} (hx : 0 < x) :
    deltaSpike ν ε x = ε⁻¹ * ν (x ^ ε⁻¹) := by
  simp [deltaSpike_def, hx]

@[simp]
theorem deltaSpike_of_nonpos (ν : ℝ → ℝ) (ε : ℝ) {x : ℝ} (hx : x ≤ 0) :
    deltaSpike ν ε x = 0 := by
  simp [deltaSpike_def, not_lt_of_ge hx]

/-- `deltaSpike ν ε` vanishes at `0`. -/
theorem deltaSpike_zero (ν : ℝ → ℝ) (ε : ℝ) : deltaSpike ν ε 0 = 0 :=
  deltaSpike_of_nonpos ν ε le_rfl

/-- At scale `ε = 1`, `deltaSpike ν 1` agrees with `ν` on `(0, ∞)`. -/
theorem deltaSpike_one (ν : ℝ → ℝ) {x : ℝ} (hx : 0 < x) : deltaSpike ν 1 x = ν x := by
  simp [hx]

/-- A nonnegative bump produces a nonnegative delta spike for `0 ≤ ε`. -/
theorem deltaSpike_nonneg {ν : ℝ → ℝ} (hν : ∀ x, 0 ≤ ν x) {ε : ℝ} (hε : 0 ≤ ε) (x : ℝ) :
    0 ≤ deltaSpike ν ε x := by
  rw [deltaSpike_def]
  split_ifs
  · exact mul_nonneg (inv_nonneg.mpr hε) (hν _)
  · exact le_rfl

/-- If `ν` is supported in `[a, b]` with `0 < a`, then for `ε > 0`, `deltaSpike ν ε` is supported
in `[a ^ ε, b ^ ε]`. -/
theorem support_deltaSpike_subset {ν : ℝ → ℝ} {a b ε : ℝ} (ha : 0 < a) (hε : 0 < ε)
    (hν : Function.support ν ⊆ Icc a b) :
    Function.support (deltaSpike ν ε) ⊆ Icc (a ^ ε) (b ^ ε) := by
  intro x hx
  have hx0 : 0 < x := by
    by_contra hle
    exact hx (deltaSpike_of_nonpos ν ε (le_of_not_gt hle))
  have hνx : ν (x ^ ε⁻¹) ≠ 0 := by
    intro h0
    exact hx (by simp [hx0, h0])
  have hmem := hν hνx
  have hcancel : (x ^ ε⁻¹) ^ ε = x := by
    rw [← Real.rpow_mul hx0.le, inv_mul_cancel₀ hε.ne', Real.rpow_one]
  refine ⟨?_, ?_⟩
  · calc a ^ ε ≤ (x ^ ε⁻¹) ^ ε := Real.rpow_le_rpow ha.le hmem.1 hε.le
      _ = x := hcancel
  · calc x = (x ^ ε⁻¹) ^ ε := hcancel.symm
      _ ≤ b ^ ε := Real.rpow_le_rpow (ha.le.trans hmem.1) hmem.2 hε.le

/-- If `ν` is supported in `[1 / 2, 2]`, then for `ε > 0`, `deltaSpike ν ε` is supported in
`[2 ^ (-ε), 2 ^ ε]`. -/
theorem support_deltaSpike_subset_two_rpow {ν : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hν : Function.support ν ⊆ Icc (1 / 2) 2) :
    Function.support (deltaSpike ν ε) ⊆ Icc (2 ^ (-ε)) (2 ^ ε) := by
  have hhalf : (1 / 2 : ℝ) ^ ε = 2 ^ (-ε) := by
    rw [one_div, Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num)]
  simpa only [hhalf] using support_deltaSpike_subset (by norm_num) hε hν

/-- Pointwise identity rewriting `deltaSpike ν ε x / x` as the Jacobian pullback of `y ↦ ν y / y`
under `y = x ^ ε⁻¹` for `x > 0`. -/
private lemma deltaSpike_div_eq_rpow_pullback (ν : ℝ → ℝ) {ε x : ℝ} (hx : 0 < x) :
    deltaSpike ν ε x / x = (ε⁻¹ * x ^ (ε⁻¹ - 1)) • (ν (x ^ ε⁻¹) / x ^ ε⁻¹) := by
  rw [deltaSpike_of_pos ν ε hx, smul_eq_mul, Real.rpow_sub hx, Real.rpow_one]
  have hne : x ^ ε⁻¹ ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
  field_simp [hne, hx.ne']

/-- For `ε > 0`, `deltaSpike ν ε` has the same `dx/x`-integral over `(0, ∞)` as `ν`, with no
integrability assumption. -/
theorem integral_deltaSpike_div (ν : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∫ x in Ioi (0 : ℝ), deltaSpike ν ε x / x = ∫ y in Ioi (0 : ℝ), ν y / y := by
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun x hx ↦ deltaSpike_div_eq_rpow_pullback ν hx)]
  exact integral_comp_rpow_Ioi_of_pos (g := fun y : ℝ ↦ ν y / y) (inv_pos.mpr hε)

/-- For `ε > 0`, `x ↦ deltaSpike ν ε x / x` is integrable on `(0, ∞)` if and only if
`y ↦ ν y / y` is. -/
theorem integrableOn_deltaSpike_div_iff (ν : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun x : ℝ ↦ deltaSpike ν ε x / x) (Ioi 0) ↔
      IntegrableOn (fun y : ℝ ↦ ν y / y) (Ioi 0) := by
  have hcongr : EqOn (fun x : ℝ ↦ deltaSpike ν ε x / x)
      (fun x : ℝ ↦ (|ε⁻¹| * x ^ (ε⁻¹ - 1)) • (ν (x ^ ε⁻¹) / x ^ ε⁻¹)) (Ioi 0) := by
    intro x hx
    dsimp only
    rw [abs_of_pos (inv_pos.mpr hε), deltaSpike_div_eq_rpow_pullback ν hx]
  rw [integrableOn_congr_fun hcongr measurableSet_Ioi]
  exact integrableOn_Ioi_comp_rpow_iff (fun y : ℝ ↦ ν y / y) (inv_ne_zero hε.ne')

/-- For `ε > 0`, the Mellin transform of `deltaSpike ν ε` at `s` is `mellin ν (ε * s)`, with no
convergence assumption. -/
theorem mellin_deltaSpike (ν : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) (s : ℂ) :
    mellin (fun x : ℝ ↦ (deltaSpike ν ε x : ℂ)) s = mellin (fun x : ℝ ↦ (ν x : ℂ)) (ε * s) := by
  have heq : EqOn (fun x : ℝ ↦ (deltaSpike ν ε x : ℂ))
      (fun x : ℝ ↦ ε⁻¹ • (ν (x ^ ε⁻¹) : ℂ)) (Ioi 0) := by
    intro x hx
    dsimp only
    rw [deltaSpike_of_pos ν ε hx, Complex.ofReal_mul, Complex.real_smul]
  have h1 : mellin (fun x : ℝ ↦ (deltaSpike ν ε x : ℂ)) s =
      mellin (fun x : ℝ ↦ ε⁻¹ • (ν (x ^ ε⁻¹) : ℂ)) s := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
    simp only [heq hx]
  rw [h1, mellin_const_smul, mellin_comp_rpow (fun y : ℝ ↦ (ν y : ℂ)) s ε⁻¹,
    abs_of_pos (inv_pos.mpr hε), inv_inv, smul_smul, inv_mul_cancel₀ hε.ne', one_smul,
    Complex.ofReal_inv, div_inv_eq_mul, mul_comm]

/-- For `ε > 0`, `deltaSpike ν ε` is Mellin convergent at `s` if and only if `ν` is Mellin
convergent at `ε * s`. -/
theorem mellinConvergent_deltaSpike_iff (ν : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) (s : ℂ) :
    MellinConvergent (fun x : ℝ ↦ (deltaSpike ν ε x : ℂ)) s ↔
      MellinConvergent (fun x : ℝ ↦ (ν x : ℂ)) (ε * s) := by
  have heq : EqOn (fun x : ℝ ↦ (x : ℂ) ^ (s - 1) • (deltaSpike ν ε x : ℂ))
      (fun x : ℝ ↦ ε⁻¹ • ((x : ℂ) ^ (s - 1) • (ν (x ^ ε⁻¹) : ℂ))) (Ioi 0) := by
    intro x hx
    dsimp only
    rw [deltaSpike_of_pos ν ε hx, Complex.ofReal_mul, Complex.real_smul, smul_eq_mul, smul_eq_mul]
    ring
  rw [MellinConvergent, integrableOn_congr_fun heq measurableSet_Ioi]
  have hsmul : IntegrableOn (fun x : ℝ ↦ ε⁻¹ • ((x : ℂ) ^ (s - 1) • (ν (x ^ ε⁻¹) : ℂ))) (Ioi 0) ↔
      MellinConvergent (fun x : ℝ ↦ (ν (x ^ ε⁻¹) : ℂ)) s := by
    simpa only [IntegrableOn, MellinConvergent, Pi.smul_def] using
      integrable_smul_iff (inv_ne_zero hε.ne')
        (f := fun x : ℝ ↦ (x : ℂ) ^ (s - 1) • (ν (x ^ ε⁻¹) : ℂ)) (μ := volume.restrict (Ioi 0))
  rw [hsmul, MellinConvergent.comp_rpow (f := fun y : ℝ ↦ (ν y : ℂ)) (inv_ne_zero hε.ne'),
    Complex.ofReal_inv, div_inv_eq_mul, mul_comm]

/-- If `ν` is supported in `[a, b]` with `0 < a` and `x ↦ ν x / x` is integrable on `(0, ∞)`,
then `ν` is integrable on `[a, b]` and Mellin convergent at every `s : ℂ`. -/
theorem mellinConvergent_of_support_subset_of_integrableOn_div {ν : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hsupp : Function.support ν ⊆ Icc a b) (hint : IntegrableOn (fun x : ℝ ↦ ν x / x) (Ioi 0))
    (s : ℂ) :
    MellinConvergent (fun x : ℝ ↦ (ν x : ℂ)) s := by
  have hint_Icc : IntegrableOn (fun x : ℝ ↦ (ν x : ℂ)) (Icc a b) := by
    have hdiv_Icc : IntegrableOn (fun x : ℝ ↦ ν x / x) (Icc a b) :=
      hint.mono_set fun x (hx : x ∈ Icc a b) ↦ ha.trans_le hx.1
    have hmul : IntegrableOn (fun x : ℝ ↦ x * (ν x / x)) (Icc a b) := by
      refine hdiv_Icc.bdd_mul (c := b) (continuous_id.aestronglyMeasurable) ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      rw [Real.norm_eq_abs, abs_of_pos (ha.trans_le hx.1)]
      exact hx.2
    have hν_Icc : IntegrableOn ν (Icc a b) := by
      refine hmul.congr_fun (fun x hx ↦ ?_) measurableSet_Icc
      exact mul_div_cancel₀ (ν x) (ha.trans_le hx.1).ne'
    exact hν_Icc.ofReal
  have hsupp_c : Function.support (fun x : ℝ ↦ (ν x : ℂ)) ⊆ Icc a b := by
    intro x hx
    exact hsupp fun h0 ↦ hx (by simp [h0])
  exact mellinConvergent_of_integrableOn_support_subset ha hint_Icc hsupp_c s

/-- Elementary pointwise bound `|x ^ ε - 1| ≤ max (log a⁻¹) (b * log b) * ε` for `x ∈ [a, b]`
(`0 < a`) and `0 ≤ ε ≤ 1`. -/
private lemma abs_rpow_sub_one_le {a b x ε : ℝ} (ha : 0 < a) (hx : x ∈ Icc a b)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    |x ^ ε - 1| ≤ max (Real.log a⁻¹) (b * Real.log b) * ε := by
  have hx0 : 0 < x := ha.trans_le hx.1
  rcases le_or_gt 1 x with hx1 | hx1
  · have hge : 1 ≤ x ^ ε := Real.one_le_rpow hx1 hε0
    rw [abs_of_nonneg (sub_nonneg.mpr hge)]
    have hexp := Real.add_one_le_exp (-(ε * Real.log x))
    have hinv : Real.exp (-(ε * Real.log x)) = (x ^ ε)⁻¹ := by
      rw [Real.exp_neg, Real.rpow_def_of_pos hx0, mul_comm]
    rw [hinv] at hexp
    have hmul : (-(ε * Real.log x) + 1) * x ^ ε ≤ 1 := by
      have hpos : 0 < x ^ ε := Real.rpow_pos_of_pos hx0 ε
      simpa only [inv_mul_cancel₀ hpos.ne'] using mul_le_mul_of_nonneg_right hexp hpos.le
    have hsub : x ^ ε - 1 ≤ x ^ ε * Real.log x * ε := by linarith
    have hb1 : 1 ≤ b := hx1.trans hx.2
    have hpow : x ^ ε ≤ b := by
      calc x ^ ε ≤ b ^ ε := Real.rpow_le_rpow hx0.le hx.2 hε0
        _ ≤ b ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hb1 hε1
        _ = b := Real.rpow_one b
    have hlog : Real.log x ≤ Real.log b := Real.log_le_log hx0 hx.2
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hprod : x ^ ε * Real.log x ≤ b * Real.log b :=
      mul_le_mul hpow hlog hlog0 (by positivity)
    exact hsub.trans (mul_le_mul_of_nonneg_right (hprod.trans (le_max_right _ _)) hε0)
  · have hle : x ^ ε ≤ 1 := Real.rpow_le_one hx0.le hx1.le hε0
    rw [abs_of_nonpos (sub_nonpos.mpr hle), neg_sub]
    have hexp := Real.add_one_le_exp (ε * Real.log x)
    rw [mul_comm ε, ← Real.rpow_def_of_pos hx0] at hexp
    have hsub : 1 - x ^ ε ≤ Real.log x⁻¹ * ε := by
      rw [Real.log_inv]
      linarith
    have hlog : Real.log x⁻¹ ≤ Real.log a⁻¹ :=
      Real.log_le_log (inv_pos.mpr hx0) (inv_anti₀ ha hx.1)
    exact hsub.trans (mul_le_mul_of_nonneg_right (hlog.trans (le_max_left _ _)) hε0)

/-- Quantitative linear bound on `‖mellin ν ε - 1‖` for a nonnegative unit-mass bump supported in
`[a, b]` (`0 < a`) and `0 ≤ ε ≤ 1`. -/
theorem norm_mellin_sub_one_le_of_support_subset {ν : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hν0 : ∀ x, 0 ≤ ν x) (hsupp : Function.support ν ⊆ Icc a b)
    (hνm : ∫ x in Ioi (0 : ℝ), ν x / x = 1) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ‖mellin (fun x : ℝ ↦ (ν x : ℂ)) ε - 1‖ ≤ max (Real.log a⁻¹) (b * Real.log b) * ε := by
  have hint : IntegrableOn (fun x : ℝ ↦ ν x / x) (Ioi 0) :=
    integrable_of_integral_eq_one hνm
  have hmc : MellinConvergent (fun x : ℝ ↦ (ν x : ℂ)) ε :=
    mellinConvergent_of_support_subset_of_integrableOn_div ha hsupp hint ε
  have hdiff : mellin (fun x : ℝ ↦ (ν x : ℂ)) ε - 1 =
      ((∫ x in Ioi (0 : ℝ), (x ^ ε - 1) * (ν x / x) : ℝ) : ℂ) := by
    have hone : (1 : ℂ) = ∫ x in Ioi (0 : ℝ), ((ν x / x : ℝ) : ℂ) := by
      rw [integral_complex_ofReal, hνm, Complex.ofReal_one]
    have hcoe : ((∫ x in Ioi (0 : ℝ), (x ^ ε - 1) * (ν x / x) : ℝ) : ℂ) =
        ∫ x in Ioi (0 : ℝ), (((x ^ ε - 1) * (ν x / x) : ℝ) : ℂ) :=
      integral_complex_ofReal.symm
    have hmc' : IntegrableOn (fun x : ℝ ↦ (x : ℂ) ^ ((ε : ℂ) - 1) • (ν x : ℂ)) (Ioi 0) := hmc
    have hint' : IntegrableOn (fun x : ℝ ↦ ((ν x / x : ℝ) : ℂ)) (Ioi 0) := hint.ofReal
    rw [hcoe]
    conv_lhs => rw [hone]
    rw [mellin, ← integral_sub hmc' hint']
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
    have hx0 : 0 < x := hx
    rw [smul_eq_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_cpow hx0.le,
      Real.rpow_sub hx0, Real.rpow_one]
    push_cast
    ring
  rw [hdiff, Complex.norm_real, Real.norm_eq_abs]
  set C : ℝ := max (Real.log a⁻¹) (b * Real.log b)
  have hint_sub : IntegrableOn (fun x : ℝ ↦ (x ^ ε - 1) * (ν x / x)) (Ioi 0) := by
    have hre : IntegrableOn
        (fun x : ℝ ↦ ((x : ℂ) ^ ((ε : ℂ) - 1) • (ν x : ℂ) - ((ν x / x : ℝ) : ℂ)).re) (Ioi 0) :=
      Complex.reCLM.integrable_comp (hmc.sub hint.ofReal)
    refine hre.congr_fun (fun x hx ↦ ?_) measurableSet_Ioi
    have hx0 : 0 < x := hx
    dsimp only
    rw [smul_eq_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_cpow hx0.le,
      Real.rpow_sub hx0, Real.rpow_one, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
      Complex.ofReal_re]
    ring
  calc |∫ x in Ioi (0 : ℝ), (x ^ ε - 1) * (ν x / x)|
      ≤ ∫ x in Ioi (0 : ℝ), |(x ^ ε - 1) * (ν x / x)| := abs_integral_le_integral_abs
    _ ≤ ∫ x in Ioi (0 : ℝ), (C * ε) * (ν x / x) := by
        refine setIntegral_mono_on hint_sub.abs (hint.const_mul (C * ε)) measurableSet_Ioi
          fun x hx ↦ ?_
        have hx0 : 0 < x := hx
        by_cases hmem : x ∈ Icc a b
        · rw [abs_mul, abs_of_nonneg (div_nonneg (hν0 x) hx0.le)]
          exact mul_le_mul_of_nonneg_right (abs_rpow_sub_one_le ha hmem hε0 hε1)
            (div_nonneg (hν0 x) hx0.le)
        · have h0 : ν x = 0 := Function.notMem_support.mp fun h ↦ hmem (hsupp h)
          simp [h0]
    _ = C * ε := by rw [integral_const_mul, hνm, mul_one]

/-- Specialization of `norm_mellin_sub_one_le_of_support_subset` to bumps supported in `[1 / 2, 2]`:
`‖mellin ν ε - 1‖ ≤ 2 * log 2 * ε` for `0 ≤ ε ≤ 1`. -/
theorem norm_mellin_sub_one_le {ν : ℝ → ℝ} (hν0 : ∀ x, 0 ≤ ν x)
    (hsupp : Function.support ν ⊆ Icc (1 / 2) 2) (hνm : ∫ x in Ioi (0 : ℝ), ν x / x = 1)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ‖mellin (fun x : ℝ ↦ (ν x : ℂ)) ε - 1‖ ≤ 2 * Real.log 2 * ε := by
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hmax : max (Real.log (1 / 2 : ℝ)⁻¹) (2 * Real.log 2) = 2 * Real.log 2 := by
    rw [one_div, inv_inv]
    exact max_eq_right (by linarith)
  simpa only [hmax] using
    norm_mellin_sub_one_le_of_support_subset (by norm_num) hν0 hsupp hνm hε0 hε1

/-- Pointwise approximation bound for `mellinConv (deltaSpike ν ε) f x`: if `‖f (x / y) - f x‖ ≤ δ`
on the support `[a ^ ε, b ^ ε]` of `deltaSpike ν ε`, then the convolution is within `δ` of `f x`. -/
theorem norm_mellinConv_deltaSpike_sub_le {ν : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hν0 : ∀ y, 0 ≤ ν y) (hsupp : Function.support ν ⊆ Icc a b)
    (hνm : ∫ y in Ioi (0 : ℝ), ν y / y = 1) {f : ℝ → ℂ}
    (hmeas : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    {ε x δ : ℝ} (hε : 0 < ε) (hx : 0 < x)
    (hbound : ∀ y ∈ Icc (a ^ ε) (b ^ ε), ‖f (x / y) - f x‖ ≤ δ) :
    ‖mellinConv (fun y : ℝ ↦ (deltaSpike ν ε y : ℂ)) f x - f x‖ ≤ δ := by
  have hint_ν : IntegrableOn (fun y : ℝ ↦ ν y / y) (Ioi 0) :=
    integrable_of_integral_eq_one hνm
  have hint_δ : IntegrableOn (fun y : ℝ ↦ deltaSpike ν ε y / y) (Ioi 0) :=
    (integrableOn_deltaSpike_div_iff ν hε).mpr hint_ν
  have hmass_δ : ∫ y in Ioi (0 : ℝ), deltaSpike ν ε y / y = 1 := by
    rw [integral_deltaSpike_div ν hε, hνm]
  have hsupp_δ : Function.support (deltaSpike ν ε) ⊆ Icc (a ^ ε) (b ^ ε) :=
    support_deltaSpike_subset ha hε hsupp
  have hint_δc : IntegrableOn (fun y : ℝ ↦ ((deltaSpike ν ε y / y : ℝ) : ℂ)) (Ioi 0) :=
    hint_δ.ofReal
  have hmeas_div : AEStronglyMeasurable (fun y : ℝ ↦ f (x / y)) (volume.restrict (Ioi 0)) :=
    hmeas.comp_quasiMeasurePreserving (quasiMeasurePreserving_div_left_Ioi hx)
  have hmeas_diff : AEStronglyMeasurable
      (fun y : ℝ ↦ (deltaSpike ν ε y : ℂ) * (f (x / y) - f x) / y) (volume.restrict (Ioi 0)) := by
    refine (hint_δc.aestronglyMeasurable.mul
      (hmeas_div.sub (aestronglyMeasurable_const (b := f x)))).congr
        (Eventually.of_forall fun y ↦ ?_)
    dsimp only [Pi.mul_apply, Pi.sub_apply]
    push_cast
    ring
  have hpw : ∀ y ∈ Ioi (0 : ℝ),
      ‖(deltaSpike ν ε y : ℂ) * (f (x / y) - f x) / y‖ ≤ δ * (deltaSpike ν ε y / y) := by
    intro y hy
    have hy0 : 0 < y := hy
    have hnn : 0 ≤ deltaSpike ν ε y / y := div_nonneg (deltaSpike_nonneg hν0 hε.le y) hy0.le
    by_cases hmem : y ∈ Icc (a ^ ε) (b ^ ε)
    · rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg (deltaSpike_nonneg hν0 hε.le y), abs_of_pos hy0,
        mul_div_right_comm, mul_comm (deltaSpike ν ε y / y)]
      exact mul_le_mul_of_nonneg_right (hbound y hmem) hnn
    · have h0 : deltaSpike ν ε y = 0 := Function.notMem_support.mp fun h ↦ hmem (hsupp_δ h)
      simp [h0]
  have hint_diff : IntegrableOn
      (fun y : ℝ ↦ (deltaSpike ν ε y : ℂ) * (f (x / y) - f x) / y) (Ioi 0) := by
    refine (hint_δ.const_mul δ).mono' hmeas_diff ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact hpw y hy
  have hint_const : IntegrableOn (fun y : ℝ ↦ (deltaSpike ν ε y : ℂ) * f x / y) (Ioi 0) := by
    refine IntegrableOn.congr_fun (hint_δc.mul_const (f x)) (fun y _ ↦ ?_) measurableSet_Ioi
    push_cast
    ring
  have hint_conv : IntegrableOn (fun y : ℝ ↦ (deltaSpike ν ε y : ℂ) * f (x / y) / y) (Ioi 0) := by
    refine (hint_diff.add hint_const).congr_fun (fun y _ ↦ ?_) measurableSet_Ioi
    rw [Pi.add_apply]
    ring
  have hfx : f x = ∫ y in Ioi (0 : ℝ), (deltaSpike ν ε y : ℂ) * f x / y := by
    have h1 : (∫ y in Ioi (0 : ℝ), (deltaSpike ν ε y : ℂ) * f x / y) =
        (∫ y in Ioi (0 : ℝ), ((deltaSpike ν ε y / y : ℝ) : ℂ)) * f x := by
      rw [← integral_mul_const]
      refine setIntegral_congr_fun measurableSet_Ioi fun y _ ↦ ?_
      push_cast
      ring
    have h2 : (∫ y in Ioi (0 : ℝ), ((deltaSpike ν ε y / y : ℝ) : ℂ)) = (1 : ℂ) := by
      rw [integral_complex_ofReal, hmass_δ, Complex.ofReal_one]
    rw [h1, h2, one_mul]
  have hsub : mellinConv (fun y : ℝ ↦ (deltaSpike ν ε y : ℂ)) f x - f x =
      ∫ y in Ioi (0 : ℝ), (deltaSpike ν ε y : ℂ) * (f (x / y) - f x) / y := by
    rw [mellinConv_def]
    conv_lhs => rw [hfx]
    rw [← integral_sub hint_conv hint_const]
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ ↦ ?_
    ring
  rw [hsub]
  calc ‖∫ y in Ioi (0 : ℝ), (deltaSpike ν ε y : ℂ) * (f (x / y) - f x) / y‖
      ≤ ∫ y in Ioi (0 : ℝ), ‖(deltaSpike ν ε y : ℂ) * (f (x / y) - f x) / y‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ y in Ioi (0 : ℝ), δ * (deltaSpike ν ε y / y) :=
        setIntegral_mono_on hint_diff.norm (hint_δ.const_mul δ) measurableSet_Ioi hpw
    _ = δ := by rw [integral_const_mul, hmass_δ, mul_one]

/-- Support upper endpoint is positive whenever a bump supported in `[a, b]` (`0 < a`) has
nonzero `dx/x`-mass. -/
private lemma pos_of_support_subset_of_integral_div_eq_one {ν : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hsupp : Function.support ν ⊆ Icc a b) (hνm : ∫ y in Ioi (0 : ℝ), ν y / y = 1) :
    0 < b := by
  by_contra hle
  have hba : b < a := (le_of_not_gt hle).trans_lt ha
  rw [Icc_eq_empty_of_lt hba, subset_empty_iff, Function.support_eq_empty_iff] at hsupp
  simp [hsupp] at hνm

/-- For `a, b > 0`, the interval `[a ^ ε, b ^ ε]` shrinks into any neighborhood `(1 - η, 1 + η)`
of `1` as `ε → 0⁺`. -/
private lemma eventually_Icc_rpow_subset {a b η : ℝ} (ha : 0 < a) (hb : 0 < b) (hη : 0 < η) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ Icc (a ^ ε) (b ^ ε), |y - 1| < η := by
  have ha_tend : Tendsto (fun ε : ℝ ↦ a ^ ε) (𝓝[>] 0) (𝓝 1) := by
    have hc : ContinuousAt (fun ε : ℝ ↦ a ^ ε) 0 :=
      (Real.continuousAt_const_rpow ha.ne')
    simpa only [Real.rpow_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hb_tend : Tendsto (fun ε : ℝ ↦ b ^ ε) (𝓝[>] 0) (𝓝 1) := by
    have hc : ContinuousAt (fun ε : ℝ ↦ b ^ ε) 0 :=
      (Real.continuousAt_const_rpow hb.ne')
    simpa only [Real.rpow_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have h1 := ha_tend.eventually (Ioo_mem_nhds (by linarith : 1 - η < 1) (by linarith : 1 < 1 + η))
  have h2 := hb_tend.eventually (Ioo_mem_nhds (by linarith : 1 - η < 1) (by linarith : 1 < 1 + η))
  filter_upwards [h1, h2] with ε haε hbε y hy
  rw [abs_lt]
  constructor <;> linarith [haε.1, haε.2, hbε.1, hbε.2, hy.1, hy.2]

/-- Pointwise approximate identity for `mellinConv`: for a nonnegative unit-mass bump supported in
`[a, b]` (`0 < a`), `mellinConv (deltaSpike ν ε) f x → f x` as `ε → 0⁺` at every point `x > 0`
where `f` is continuous (assuming `f` is a.e. strongly measurable on `(0, ∞)`). -/
theorem tendsto_mellinConv_deltaSpike {ν : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hν0 : ∀ y, 0 ≤ ν y) (hsupp : Function.support ν ⊆ Icc a b)
    (hνm : ∫ y in Ioi (0 : ℝ), ν y / y = 1) {f : ℝ → ℂ}
    (hmeas : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    {x : ℝ} (hx : 0 < x) (hcont : ContinuousAt f x) :
    Tendsto (fun ε : ℝ ↦ mellinConv (fun y : ℝ ↦ (deltaSpike ν ε y : ℂ)) f x)
      (𝓝[>] 0) (𝓝 (f x)) := by
  have hb : 0 < b := pos_of_support_subset_of_integral_div_eq_one ha hsupp hνm
  rw [Metric.tendsto_nhds]
  intro δ hδ
  have hcomp : ContinuousAt (fun y : ℝ ↦ f (x / y)) 1 := by
    have hdiv : ContinuousAt (fun y : ℝ ↦ x / y) 1 :=
      continuousAt_const.div continuousAt_id one_ne_zero
    have hcont1 : ContinuousAt f (x / 1) := by simpa only [div_one] using hcont
    exact hcont1.comp hdiv
  obtain ⟨η, hη, hball⟩ := Metric.continuousAt_iff.mp hcomp (δ / 2) (half_pos hδ)
  filter_upwards [self_mem_nhdsWithin, eventually_Icc_rpow_subset ha hb hη] with ε hε hsub
  rw [dist_eq_norm]
  have hle : ‖mellinConv (fun y : ℝ ↦ (deltaSpike ν ε y : ℂ)) f x - f x‖ ≤ δ / 2 := by
    refine norm_mellinConv_deltaSpike_sub_le ha hν0 hsupp hνm hmeas hε hx fun y hy ↦ ?_
    have hlt := hball (by simpa only [Real.dist_eq] using hsub y hy)
    rw [div_one, dist_eq_norm] at hlt
    exact hlt.le
  linarith

/-- Uniform approximate identity on compact subsets of `(0, ∞)`: when `f` is continuous on
`(0, ∞)`, `mellinConv (deltaSpike ν ε) f` converges uniformly to `f` on every compact `K ⊆ (0, ∞)`
as `ε → 0⁺`. -/
theorem tendstoUniformlyOn_mellinConv_deltaSpike {ν : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hν0 : ∀ y, 0 ≤ ν y) (hsupp : Function.support ν ⊆ Icc a b)
    (hνm : ∫ y in Ioi (0 : ℝ), ν y / y = 1) {f : ℝ → ℂ} (hcont : ContinuousOn f (Ioi 0))
    {K : Set ℝ} (hK : IsCompact K) (hKpos : K ⊆ Ioi 0) :
    TendstoUniformlyOn (fun ε x ↦ mellinConv (fun y : ℝ ↦ (deltaSpike ν ε y : ℂ)) f x)
      f (𝓝[>] 0) K := by
  have hb : 0 < b := pos_of_support_subset_of_integral_div_eq_one ha hsupp hνm
  rw [Metric.tendstoUniformlyOn_iff]
  intro δ hδ
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact Eventually.of_forall fun _ _ hx ↦ hx.elim
  obtain ⟨x₁, hx₁K, hx₁min⟩ := hK.exists_isMinOn hKne continuousOn_id
  obtain ⟨x₂, hx₂K, hx₂max⟩ := hK.exists_isMaxOn hKne continuousOn_id
  have hx₁0 : 0 < x₁ := hKpos hx₁K
  have hx₂0 : 0 < x₂ := hKpos hx₂K
  have hK'sub : Icc (x₁ / 2) (2 * x₂) ⊆ Ioi 0 := fun _ hu ↦ mem_Ioi.mpr (by linarith [hu.1, hx₁0])
  have hunif : UniformContinuousOn f (Icc (x₁ / 2) (2 * x₂)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous (hcont.mono hK'sub)
  obtain ⟨η, hη, hη_bound⟩ := Metric.uniformContinuousOn_iff.mp hunif (δ / 2) (half_pos hδ)
  let ρ : ℝ := min (1 / 2) (η / (2 * x₂))
  have hρ : 0 < ρ := lt_min (by norm_num) (by positivity)
  have hmeas : AEStronglyMeasurable f (volume.restrict (Ioi 0)) :=
    hcont.aestronglyMeasurable measurableSet_Ioi
  filter_upwards [self_mem_nhdsWithin, eventually_Icc_rpow_subset ha hb hρ] with ε hε hsub x hxK
  have hx0 : 0 < x := hKpos hxK
  have hx_ge : x₁ ≤ x := hx₁min hxK
  have hx_le : x ≤ x₂ := hx₂max hxK
  rw [dist_comm, dist_eq_norm]
  have hle : ‖mellinConv (fun y : ℝ ↦ (deltaSpike ν ε y : ℂ)) f x - f x‖ ≤ δ / 2 := by
    refine norm_mellinConv_deltaSpike_sub_le ha hν0 hsupp hνm hmeas hε hx0 fun y hy ↦ ?_
    have hy_close : |y - 1| < ρ := hsub y hy
    have hy_lo : 1 / 2 < y := by
      have h1 : |y - 1| < 1 / 2 := hy_close.trans_le (min_le_left _ _)
      linarith [(abs_lt.mp h1).1]
    have hy_hi : y < 2 := by
      have h1 : |y - 1| < 1 / 2 := hy_close.trans_le (min_le_left _ _)
      linarith [(abs_lt.mp h1).2]
    have hy0 : 0 < y := by linarith
    have hxmem : x ∈ Icc (x₁ / 2) (2 * x₂) := ⟨by linarith, by linarith⟩
    have hdivmem : x / y ∈ Icc (x₁ / 2) (2 * x₂) := by
      refine ⟨?_, ?_⟩
      · rw [le_div_iff₀ hy0]
        nlinarith
      · rw [div_le_iff₀ hy0]
        nlinarith
    have hdist : dist (x / y) x < η := by
      rw [Real.dist_eq]
      have hfrac : x / y - x = x * (1 - y) / y := by field_simp [hy0.ne']
      rw [hfrac, abs_div, abs_mul, abs_of_pos hx0, abs_of_pos hy0, abs_sub_comm]
      have h1 : |y - 1| < η / (2 * x₂) := hy_close.trans_le (min_le_right _ _)
      rw [div_lt_iff₀ hy0]
      have hmul : x * |y - 1| < x₂ * (η / (2 * x₂)) := by
        calc x * |y - 1| ≤ x₂ * |y - 1| := mul_le_mul_of_nonneg_right hx_le (abs_nonneg _)
          _ < x₂ * (η / (2 * x₂)) := mul_lt_mul_of_pos_left h1 hx₂0
      have hsimp : x₂ * (η / (2 * x₂)) = η / 2 := by field_simp [hx₂0.ne']
      nlinarith
    have hlt := hη_bound (x / y) hdivmem x hxmem hdist
    rw [dist_eq_norm] at hlt
    exact hlt.le
  linarith

/-! ### Smoothed cutoffs -/

/-- The smoothed cutoff associated to a bump `ν : ℝ → ℝ` at scale `ε`:
`∫ z in Ioi x, deltaSpike ν ε z / z` for `x > 0`, and `0` for `x ≤ 0`. -/
noncomputable def smoothCutoff (ν : ℝ → ℝ) (ε x : ℝ) : ℝ :=
  if 0 < x then ∫ z in Ioi x, deltaSpike ν ε z / z else 0

/-- Unfolding lemma for `smoothCutoff`. -/
theorem smoothCutoff_def (ν : ℝ → ℝ) (ε x : ℝ) :
    smoothCutoff ν ε x = if 0 < x then ∫ z in Ioi x, deltaSpike ν ε z / z else 0 := (rfl)

@[simp]
theorem smoothCutoff_of_pos (ν : ℝ → ℝ) (ε : ℝ) {x : ℝ} (hx : 0 < x) :
    smoothCutoff ν ε x = ∫ z in Ioi x, deltaSpike ν ε z / z := by
  simp [smoothCutoff_def, hx]

@[simp]
theorem smoothCutoff_of_nonpos (ν : ℝ → ℝ) (ε : ℝ) {x : ℝ} (hx : x ≤ 0) :
    smoothCutoff ν ε x = 0 := by
  simp [smoothCutoff_def, not_lt_of_ge hx]

/-- `smoothCutoff ν ε` vanishes at `0`. -/
theorem smoothCutoff_zero (ν : ℝ → ℝ) (ε : ℝ) : smoothCutoff ν ε 0 = 0 :=
  smoothCutoff_of_nonpos ν ε le_rfl

/-- Change of variables `y = z ^ ε⁻¹` expresses `smoothCutoff ν ε x` directly in terms of `ν` for
`ε > 0` and `x > 0`, with no integrability hypothesis. -/
theorem smoothCutoff_eq_integral_rpow (ν : ℝ → ℝ) {ε x : ℝ} (hε : 0 < ε) (hx : 0 < x) :
    smoothCutoff ν ε x = ∫ y in Ioi (x ^ ε⁻¹), ν y / y := by
  rw [smoothCutoff_of_pos ν ε hx]
  have hcancel : (x ^ ε⁻¹) ^ (ε⁻¹)⁻¹ = x := by
    rw [inv_inv, ← Real.rpow_mul hx.le, inv_mul_cancel₀ hε.ne', Real.rpow_one]
  have hsub := integral_comp_rpow_Ioi_of_pos' (g := fun y : ℝ ↦ ν y / y) (inv_pos.mpr hε)
    (Real.rpow_nonneg hx.le ε⁻¹)
  rw [hcancel] at hsub
  rw [← hsub]
  refine setIntegral_congr_fun measurableSet_Ioi fun z hz ↦ ?_
  exact deltaSpike_div_eq_rpow_pullback ν (hx.trans hz)

/-- For `x > 0`, `smoothCutoff ν ε x` is the Mellin convolution of `1_(0,1]` with
`deltaSpike ν ε`, with no integrability hypothesis. -/
theorem smoothCutoff_eq_mellinConv (ν : ℝ → ℝ) (ε : ℝ) {x : ℝ} (hx : 0 < x) :
    (smoothCutoff ν ε x : ℂ) =
      mellinConv ((Ioc 0 1).indicator 1) (fun y : ℝ ↦ (deltaSpike ν ε y : ℂ)) x := by
  rw [smoothCutoff_of_pos ν ε hx, mellinConv_indicator_Ioc_one _ hx]
  have hcoe : ((∫ z in Ioi x, deltaSpike ν ε z / z : ℝ) : ℂ) =
      ∫ z in Ioi x, ((deltaSpike ν ε z / z : ℝ) : ℂ) :=
    integral_complex_ofReal.symm
  rw [hcoe]
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ ↦ ?_
  simp

/-- A nonnegative bump yields a nonnegative smoothed cutoff for `0 ≤ ε`. -/
theorem smoothCutoff_nonneg {ν : ℝ → ℝ} (hν0 : ∀ x, 0 ≤ ν x) {ε : ℝ} (hε : 0 ≤ ε) (x : ℝ) :
    0 ≤ smoothCutoff ν ε x := by
  rw [smoothCutoff_def]
  split_ifs with hx
  · refine setIntegral_nonneg measurableSet_Ioi fun z hz ↦ ?_
    exact div_nonneg (deltaSpike_nonneg hν0 hε z) (hx.trans hz).le
  · exact le_rfl

/-- For a nonnegative integrable bump and `ε > 0`, `smoothCutoff ν ε x` is bounded above by the
total `dx/x`-mass `∫₀^∞ ν(y) dy/y`. -/
theorem smoothCutoff_le_integral_div {ν : ℝ → ℝ} (hν0 : ∀ x, 0 ≤ ν x)
    (hint : IntegrableOn (fun x : ℝ ↦ ν x / x) (Ioi 0)) {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    smoothCutoff ν ε x ≤ ∫ y in Ioi (0 : ℝ), ν y / y := by
  rcases le_or_gt x 0 with hx | hx
  · rw [smoothCutoff_of_nonpos ν ε hx]
    exact setIntegral_nonneg measurableSet_Ioi fun y hy ↦ div_nonneg (hν0 y) (le_of_lt hy)
  · rw [smoothCutoff_eq_integral_rpow ν hε hx]
    refine setIntegral_mono_set hint ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      exact div_nonneg (hν0 y) (le_of_lt hy)
    · exact Eventually.of_forall fun y hy ↦ (Real.rpow_pos_of_pos hx ε⁻¹).trans hy

/-- For a nonnegative unit-mass bump and `ε > 0`, `smoothCutoff ν ε x ≤ 1`. -/
theorem smoothCutoff_le_one {ν : ℝ → ℝ} (hν0 : ∀ x, 0 ≤ ν x)
    (hνm : ∫ x in Ioi (0 : ℝ), ν x / x = 1) {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    smoothCutoff ν ε x ≤ 1 := by
  simpa only [hνm] using smoothCutoff_le_integral_div hν0 (integrable_of_integral_eq_one hνm) hε x

/-- For a nonnegative integrable bump and `ε > 0`, `smoothCutoff ν ε` is antitone on `(0, ∞)`. -/
theorem smoothCutoff_antitoneOn {ν : ℝ → ℝ} (hν0 : ∀ x, 0 ≤ ν x)
    (hint : IntegrableOn (fun x : ℝ ↦ ν x / x) (Ioi 0)) {ε : ℝ} (hε : 0 < ε) :
    AntitoneOn (smoothCutoff ν ε) (Ioi 0) := by
  intro x hx y hy hxy
  rw [smoothCutoff_eq_integral_rpow ν hε hx, smoothCutoff_eq_integral_rpow ν hε hy]
  have hpow : x ^ ε⁻¹ ≤ y ^ ε⁻¹ := Real.rpow_le_rpow (le_of_lt hx) hxy (inv_pos.mpr hε).le
  refine setIntegral_mono_set (hint.mono_set fun z (hz : z ∈ Ioi (x ^ ε⁻¹)) ↦
      (Real.rpow_pos_of_pos hx ε⁻¹).trans hz) ?_ ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    exact div_nonneg (hν0 z) ((Real.rpow_pos_of_pos hx ε⁻¹).trans hz).le
  · exact Eventually.of_forall fun z hz ↦ hpow.trans_lt hz

/-- If `ν` is supported in `[a, b]` (`0 < a`) with `dx/x`-mass `1`, then `smoothCutoff ν ε x = 1`
for all `0 < x ≤ a ^ ε`. -/
theorem smoothCutoff_eq_one_of_le {ν : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hsupp : Function.support ν ⊆ Icc a b) (hνm : ∫ x in Ioi (0 : ℝ), ν x / x = 1)
    {ε x : ℝ} (hε : 0 < ε) (hx0 : 0 < x) (hxa : x ≤ a ^ ε) :
    smoothCutoff ν ε x = 1 := by
  rw [smoothCutoff_eq_integral_rpow ν hε hx0, ← hνm, ← integral_Ici_eq_integral_Ioi]
  have hpow : x ^ ε⁻¹ ≤ a := by
    calc x ^ ε⁻¹ ≤ (a ^ ε) ^ ε⁻¹ := Real.rpow_le_rpow hx0.le hxa (inv_pos.mpr hε).le
      _ = a := by rw [← Real.rpow_mul ha.le, mul_inv_cancel₀ hε.ne', Real.rpow_one]
  have hind : EqOn (fun y : ℝ ↦ ν y / y)
      ((Ici (x ^ ε⁻¹)).indicator fun y : ℝ ↦ ν y / y) (Ioi 0) := by
    intro y _
    by_cases hy : x ^ ε⁻¹ ≤ y
    · simp [hy]
    · have hnot : y ∉ Icc a b := fun h ↦ hy (hpow.trans h.1)
      have h0 : ν y = 0 := Function.notMem_support.mp fun h ↦ hnot (hsupp h)
      simp [hy, h0]
  rw [setIntegral_congr_fun measurableSet_Ioi hind, setIntegral_indicator measurableSet_Ici,
    inter_eq_right.mpr (Ici_subset_Ioi.mpr (Real.rpow_pos_of_pos hx0 ε⁻¹))]

/-- If `ν` is supported in `[a, b]` with `0 ≤ b`, then `smoothCutoff ν ε x = 0` for all
`b ^ ε ≤ x`. -/
theorem smoothCutoff_eq_zero_of_le {ν : ℝ → ℝ} {a b : ℝ} (hb : 0 ≤ b)
    (hsupp : Function.support ν ⊆ Icc a b) {ε x : ℝ} (hε : 0 < ε) (hbx : b ^ ε ≤ x) :
    smoothCutoff ν ε x = 0 := by
  rcases le_or_gt x 0 with hx | hx
  · exact smoothCutoff_of_nonpos ν ε hx
  · rw [smoothCutoff_eq_integral_rpow ν hε hx]
    have hpow : b ≤ x ^ ε⁻¹ := by
      calc b = (b ^ ε) ^ ε⁻¹ := by
            rw [← Real.rpow_mul hb, mul_inv_cancel₀ hε.ne', Real.rpow_one]
        _ ≤ x ^ ε⁻¹ := Real.rpow_le_rpow (Real.rpow_nonneg hb ε) hbx (inv_pos.mpr hε).le
    refine setIntegral_eq_zero_of_forall_eq_zero fun y hy ↦ ?_
    have hnot : y ∉ Icc a b := fun h ↦ not_lt_of_ge (h.2.trans hpow) hy
    simp [Function.notMem_support.mp fun h ↦ hnot (hsupp h)]

/-- For a multiplicatively symmetric unit-mass bump (`ν x⁻¹ = ν x` for all `x > 0`),
`smoothCutoff ν ε 1 = 1 / 2` for every `ε > 0`. -/
theorem smoothCutoff_one_of_inv {ν : ℝ → ℝ} (hinv : ∀ x : ℝ, 0 < x → ν x⁻¹ = ν x)
    (hνm : ∫ x in Ioi (0 : ℝ), ν x / x = 1) {ε : ℝ} (hε : 0 < ε) :
    smoothCutoff ν ε 1 = 1 / 2 := by
  rw [smoothCutoff_eq_integral_rpow ν hε zero_lt_one, Real.one_rpow]
  have hint : IntegrableOn (fun y : ℝ ↦ ν y / y) (Ioi 0) :=
    integrable_of_integral_eq_one hνm
  have hunion : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioi 1) :=
    Set.disjoint_left.mpr fun _ h1 h2 ↦ not_lt_of_ge h1.2 h2
  have hsplit : (∫ y in Ioi (0 : ℝ), ν y / y) =
      (∫ y in Ioc (0 : ℝ) 1, ν y / y) + ∫ y in Ioi (1 : ℝ), ν y / y := by
    rw [hunion, setIntegral_union hdisj measurableSet_Ioi
      (hint.mono_set fun _ h ↦ h.1) (hint.mono_set fun _ h ↦ zero_lt_one.trans h)]
  have hsymm : (∫ y in Ioc (0 : ℝ) 1, ν y / y) = ∫ y in Ioi (1 : ℝ), ν y / y := by
    have hcomp := integral_comp_rpow_Ioi
      ((Ioi (1 : ℝ)).indicator fun t : ℝ ↦ ν t / t) (p := (-1 : ℝ)) (by norm_num)
    have hrhs : (∫ z in Ioi (0 : ℝ), (Ioi (1 : ℝ)).indicator (fun t : ℝ ↦ ν t / t) z) =
        ∫ z in Ioi (1 : ℝ), ν z / z := by
      rw [setIntegral_indicator measurableSet_Ioi,
        inter_eq_right.mpr fun _ h ↦ zero_lt_one.trans h]
    have hlhs : EqOn
        (fun y : ℝ ↦ (|(-1 : ℝ)| * y ^ ((-1 : ℝ) - 1)) •
          (Ioi (1 : ℝ)).indicator (fun t : ℝ ↦ ν t / t) (y ^ (-1 : ℝ)))
        ((Ioo (0 : ℝ) 1).indicator fun y : ℝ ↦ ν y / y) (Ioi 0) := by
      intro y hy
      have hy0 : 0 < y := hy
      dsimp only
      rw [Real.rpow_neg_one, abs_neg, abs_one, one_mul, smul_eq_mul]
      have hpow : y ^ ((-1 : ℝ) - 1) = (y ^ 2)⁻¹ := by
        have hsub : (-1 : ℝ) - 1 = -(2 : ℝ) := by norm_num
        rw [hsub, Real.rpow_neg hy0.le, Real.rpow_two]
      rw [hpow]
      by_cases hy1 : y < 1
      · have h1 : (1 : ℝ) < y⁻¹ := one_lt_inv₀ hy0 |>.mpr hy1
        simp only [mem_Ioi, h1, indicator_of_mem, mem_Ioo, hy0, hy1, and_self]
        rw [hinv y hy0, div_inv_eq_mul]
        field_simp [hy0.ne']
      · have h1 : ¬ (1 : ℝ) < y⁻¹ := fun h ↦ hy1 ((one_lt_inv₀ hy0).mp h)
        simp [h1, hy1]
    rw [hrhs, setIntegral_congr_fun measurableSet_Ioi hlhs,
      setIntegral_indicator measurableSet_Ioo,
      inter_eq_right.mpr fun _ (h : _ ∈ Ioo 0 1) ↦ h.1, ← integral_Ioc_eq_integral_Ioo] at hcomp
    exact hcomp
  linarith

/-- For any bump with `x ↦ ν x / x` integrable on `(0, ∞)` and any `ε > 0`, `smoothCutoff ν ε` is
continuous on `(0, ∞)`. -/
theorem continuousOn_smoothCutoff {ν : ℝ → ℝ}
    (hint : IntegrableOn (fun x : ℝ ↦ ν x / x) (Ioi 0)) {ε : ℝ} (hε : 0 < ε) :
    ContinuousOn (smoothCutoff ν ε) (Ioi 0) := by
  let g : ℝ → ℝ := (Ioi (0 : ℝ)).indicator fun t : ℝ ↦ ν t / t
  have hg : Integrable g := (integrable_indicator_iff measurableSet_Ioi).mpr hint
  have hprim : Continuous fun y : ℝ ↦ (∫ t in Ioi (0 : ℝ), ν t / t) - ∫ t in (0 : ℝ)..y, g t :=
    continuous_const.sub (hg.continuous_primitive 0)
  have hcomp : ContinuousOn
      (fun x : ℝ ↦ (∫ t in Ioi (0 : ℝ), ν t / t) - ∫ t in (0 : ℝ)..(x ^ ε⁻¹), g t) (Ioi 0) :=
    hprim.comp_continuousOn (continuousOn_id.rpow_const fun x hx ↦ Or.inl (ne_of_gt hx))
  refine hcomp.congr fun x hx ↦ ?_
  have hx0 : 0 < x := hx
  have hy0 : 0 < x ^ ε⁻¹ := Real.rpow_pos_of_pos hx0 ε⁻¹
  rw [smoothCutoff_eq_integral_rpow ν hε hx0]
  have hunion : Ioi (0 : ℝ) = Ioc 0 (x ^ ε⁻¹) ∪ Ioi (x ^ ε⁻¹) :=
    (Ioc_union_Ioi_eq_Ioi hy0.le).symm
  have hdisj : Disjoint (Ioc (0 : ℝ) (x ^ ε⁻¹)) (Ioi (x ^ ε⁻¹)) :=
    Set.disjoint_left.mpr fun _ h1 h2 ↦ not_lt_of_ge h1.2 h2
  have hsplit : (∫ t in Ioi (0 : ℝ), ν t / t) =
      (∫ t in Ioc (0 : ℝ) (x ^ ε⁻¹), ν t / t) + ∫ t in Ioi (x ^ ε⁻¹), ν t / t := by
    rw [hunion, setIntegral_union hdisj measurableSet_Ioi
      (hint.mono_set fun _ h ↦ h.1) (hint.mono_set fun _ h ↦ hy0.trans h)]
  have hIoc : (∫ t in (0 : ℝ)..(x ^ ε⁻¹), g t) = ∫ t in Ioc (0 : ℝ) (x ^ ε⁻¹), ν t / t := by
    rw [intervalIntegral.integral_of_le hy0.le]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht ↦ ?_
    simp [g, ht.1]
  linarith

/-- On `Re s > 0`, `smoothCutoff ν ε` has Mellin transform `mellin ν (ε * s) / s` with absolute
convergence whenever `ν` is Mellin convergent at `ε * s`. -/
theorem hasMellin_smoothCutoff {ν : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε) {s : ℂ} (hs : 0 < s.re)
    (hν : MellinConvergent (fun x : ℝ ↦ (ν x : ℂ)) (ε * s)) :
    HasMellin (fun x : ℝ ↦ (smoothCutoff ν ε x : ℂ)) s
      (mellin (fun x : ℝ ↦ (ν x : ℂ)) (ε * s) / s) := by
  have h1 := hasMellin_one_Ioc hs
  have h2 : MellinConvergent (fun x : ℝ ↦ (deltaSpike ν ε x : ℂ)) s :=
    (mellinConvergent_deltaSpike_iff ν hε s).mpr hν
  have hconv := hasMellin_mellinConv h1.1 h2
  rw [h1.2, mellin_deltaSpike ν hε s, one_div_mul_eq_div] at hconv
  exact (hasMellin_congr (fun x hx ↦ smoothCutoff_eq_mellinConv ν ε hx)).mpr hconv

/-- Mellin transform formula for the smoothed cutoff: for `ε > 0`, `0 < Re s`, and
`MellinConvergent ν (ε * s)`, `mellin (smoothCutoff ν ε) s = mellin ν (ε * s) / s`. -/
theorem mellin_smoothCutoff {ν : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε) {s : ℂ} (hs : 0 < s.re)
    (hν : MellinConvergent (fun x : ℝ ↦ (ν x : ℂ)) (ε * s)) :
    mellin (fun x : ℝ ↦ (smoothCutoff ν ε x : ℂ)) s =
      mellin (fun x : ℝ ↦ (ν x : ℂ)) (ε * s) / s :=
  (hasMellin_smoothCutoff hε hs hν).2

/-- Uniform decay in `ε ∈ (0, 1]` on half-strips `0 < Re s ≤ σ₂` for the Mellin transform of
`smoothCutoff ν ε` when `ν` is `C^k` and supported in `[a, b]` (`0 < a`). -/
theorem norm_mellin_smoothCutoff_le {ν : ℝ → ℝ} {k : ℕ} {a b : ℝ} (ha : 0 < a)
    (hν : ContDiff ℝ k ν) (hνs : Function.support ν ⊆ Icc a b) (σ₂ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ s : ℂ, 0 < s.re → s.re ≤ σ₂ →
      ‖mellin (fun x : ℝ ↦ (smoothCutoff ν ε x : ℂ)) s‖ ≤
        C / (‖s‖ * (1 + ε * ‖s‖) ^ k) := by
  have hν_c : ContDiff ℝ k (fun x : ℝ ↦ (ν x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hν
  have hsupp_c : Function.support (fun x : ℝ ↦ (ν x : ℂ)) ⊆ Icc a b := fun x hx ↦
    hνs fun h0 ↦ hx (by simp [h0])
  obtain ⟨C, hC0, hC⟩ :=
    exists_norm_mellin_le_div_one_add_norm_pow ha hν_c hsupp_c 0 σ₂
  refine ⟨C, hC0, fun ε hε hε1 s hs h2 ↦ ?_⟩
  have hmc : MellinConvergent (fun x : ℝ ↦ (ν x : ℂ)) (ε * s) :=
    mellinConvergent_of_integrableOn_support_subset ha hν_c.continuous.integrableOn_Icc hsupp_c _
  rw [mellin_smoothCutoff hε hs hmc, norm_div]
  have hre0 : 0 ≤ ((ε : ℂ) * s).re := by
    rw [Complex.re_ofReal_mul]
    exact mul_nonneg hε.le hs.le
  have hre2 : ((ε : ℂ) * s).re ≤ σ₂ := by
    rw [Complex.re_ofReal_mul]
    calc ε * s.re ≤ 1 * s.re := mul_le_mul_of_nonneg_right hε1 hs.le
      _ ≤ σ₂ := by linarith
  have hbound := hC ((ε : ℂ) * s) hre0 hre2
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε] at hbound
  calc ‖mellin (fun x : ℝ ↦ (ν x : ℂ)) (ε * s)‖ / ‖s‖
      ≤ (C / (1 + ε * ‖s‖) ^ k) / ‖s‖ := div_le_div_of_nonneg_right hbound (norm_nonneg _)
    _ = C / (‖s‖ * (1 + ε * ‖s‖) ^ k) := by rw [div_div, mul_comm]

/-- For a `C^k` bump (`k ≥ 1`) supported in `[a, b]` (`0 < a`), `mellin (smoothCutoff ν ε)` is
integrable along every positive vertical line `Re s = σ > 0` for every `ε > 0`. -/
theorem verticalIntegrable_mellin_smoothCutoff {ν : ℝ → ℝ} {k : ℕ} {a b : ℝ} (ha : 0 < a)
    (hk : 1 ≤ k) (hν : ContDiff ℝ k ν) (hνs : Function.support ν ⊆ Icc a b)
    {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) :
    VerticalIntegrable (mellin fun x : ℝ ↦ (smoothCutoff ν ε x : ℂ)) σ := by
  have hν_c : ContDiff ℝ k (fun x : ℝ ↦ (ν x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hν
  have hsupp_c : Function.support (fun x : ℝ ↦ (ν x : ℂ)) ⊆ Icc a b := fun x hx ↦
    hνs fun h0 ↦ hx (by simp [h0])
  obtain ⟨C, hC0, hC⟩ :=
    exists_norm_mellin_le_div_one_add_norm_pow ha hν_c hsupp_c (ε * σ) (ε * σ)
  have hline : ∀ t : ℝ, mellin (fun x : ℝ ↦ (smoothCutoff ν ε x : ℂ)) (σ + t * I) =
      mellin (fun x : ℝ ↦ (ν x : ℂ)) (ε * ((σ : ℂ) + t * I)) / ((σ : ℂ) + t * I) := by
    intro t
    have hre : 0 < ((σ : ℂ) + t * I).re := by simp [hσ]
    have hmc : MellinConvergent (fun x : ℝ ↦ (ν x : ℂ)) (ε * ((σ : ℂ) + t * I)) :=
      mellinConvergent_of_integrableOn_support_subset ha hν_c.continuous.integrableOn_Icc hsupp_c _
    exact mellin_smoothCutoff hε hre hmc
  have hentire : Differentiable ℂ (mellin fun x : ℝ ↦ (ν x : ℂ)) :=
    differentiable_mellin_of_integrableOn_support_subset ha hν_c.continuous.integrableOn_Icc hsupp_c
  have hcont : Continuous fun t : ℝ ↦
      mellin (fun x : ℝ ↦ (smoothCutoff ν ε x : ℂ)) (σ + t * I) := by
    simp_rw [hline]
    refine Continuous.div ?_ (by fun_prop) fun t h0 ↦ ?_
    · exact hentire.continuous.comp (by fun_prop)
    · have hre := congrArg Complex.re h0
      simp at hre
      linarith
  let m : ℝ := min (σ ^ 2) 1
  refine (integrable_inv_one_add_sq.const_mul (C / (ε * m))).mono' hcont.aestronglyMeasurable
    (Eventually.of_forall fun t ↦ ?_)
  rw [hline t, norm_div]
  set s : ℂ := (σ : ℂ) + t * I
  have hre : ((ε : ℂ) * s).re = ε * σ := by simp [s]
  have hbound := hC ((ε : ℂ) * s) hre.ge hre.le
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε] at hbound
  have hs_sq : ‖s‖ ^ 2 = σ ^ 2 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_add_mul_I]
  have hpow_ge : ε * ‖s‖ ≤ (1 + ε * ‖s‖) ^ k := by
    calc ε * ‖s‖ ≤ 1 + ε * ‖s‖ := by linarith
      _ = (1 + ε * ‖s‖) ^ 1 := (pow_one _).symm
      _ ≤ (1 + ε * ‖s‖) ^ k := pow_le_pow_right₀ (by linarith [mul_nonneg hε.le (norm_nonneg s)]) hk
  have hdenom_ge : ε * m * (1 + t ^ 2) ≤ ‖s‖ * (1 + ε * ‖s‖) ^ k := by
    have hsq_ge : m * (1 + t ^ 2) ≤ ‖s‖ ^ 2 := by
      rw [hs_sq]
      nlinarith [min_le_left (σ ^ 2) 1, min_le_right (σ ^ 2) 1, sq_nonneg t]
    calc ε * m * (1 + t ^ 2) = ε * (m * (1 + t ^ 2)) := by ring
      _ ≤ ε * ‖s‖ ^ 2 := mul_le_mul_of_nonneg_left hsq_ge hε.le
      _ = ‖s‖ * (ε * ‖s‖) := by ring
      _ ≤ ‖s‖ * (1 + ε * ‖s‖) ^ k := mul_le_mul_of_nonneg_left hpow_ge (norm_nonneg s)
  calc ‖mellin (fun x : ℝ ↦ (ν x : ℂ)) (ε * s)‖ / ‖s‖
      ≤ (C / (1 + ε * ‖s‖) ^ k) / ‖s‖ := div_le_div_of_nonneg_right hbound (norm_nonneg s)
    _ = C / (‖s‖ * (1 + ε * ‖s‖) ^ k) := by rw [div_div, mul_comm]
    _ ≤ C / (ε * m * (1 + t ^ 2)) := by
        gcongr
    _ = C / (ε * m) * (1 + t ^ 2)⁻¹ := by rw [div_mul_eq_div_div, div_eq_mul_inv]

/-- Linear perturbation bound for `mellin (smoothCutoff ν ε) 1` when `ν` is a nonnegative
unit-mass bump supported in `[a, b]` (`0 < a`) and `0 < ε ≤ 1`. -/
theorem norm_mellin_smoothCutoff_one_sub_one_le_of_support_subset {ν : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hν0 : ∀ x, 0 ≤ ν x) (hsupp : Function.support ν ⊆ Icc a b)
    (hνm : ∫ x in Ioi (0 : ℝ), ν x / x = 1) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ‖mellin (fun x : ℝ ↦ (smoothCutoff ν ε x : ℂ)) 1 - 1‖ ≤
      max (Real.log a⁻¹) (b * Real.log b) * ε := by
  have hmc : MellinConvergent (fun x : ℝ ↦ (ν x : ℂ)) (ε * 1) :=
    mellinConvergent_of_support_subset_of_integrableOn_div ha hsupp
      (integrable_of_integral_eq_one hνm) _
  rw [mellin_smoothCutoff hε (by simp) hmc, mul_one, div_one]
  exact norm_mellin_sub_one_le_of_support_subset ha hν0 hsupp hνm hε.le hε1

/-- Specialization of `norm_mellin_smoothCutoff_one_sub_one_le_of_support_subset` to bumps
supported in `[1 / 2, 2]`: `‖mellin (smoothCutoff ν ε) 1 - 1‖ ≤ 2 * log 2 * ε`. -/
theorem norm_mellin_smoothCutoff_one_sub_one_le {ν : ℝ → ℝ} (hν0 : ∀ x, 0 ≤ ν x)
    (hsupp : Function.support ν ⊆ Icc (1 / 2) 2) (hνm : ∫ x in Ioi (0 : ℝ), ν x / x = 1)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ‖mellin (fun x : ℝ ↦ (smoothCutoff ν ε x : ℂ)) 1 - 1‖ ≤ 2 * Real.log 2 * ε := by
  have hmc : MellinConvergent (fun x : ℝ ↦ (ν x : ℂ)) (ε * 1) :=
    mellinConvergent_of_support_subset_of_integrableOn_div (by norm_num) hsupp
      (integrable_of_integral_eq_one hνm) _
  rw [mellin_smoothCutoff hε (by simp) hmc, mul_one, div_one]
  exact norm_mellin_sub_one_le hν0 hsupp hνm hε.le hε1

/-! ### Standing-bump checks -/

example {ν : ℝ → ℝ} (hνs : Function.support ν ⊆ Icc (1 / 2) 2)
    (hνm : ∫ x in Ioi (0 : ℝ), ν x / x = 1) {ε : ℝ} (hε : 0 < ε) {s : ℂ} (hs : 0 < s.re) :
    mellin (fun x ↦ (smoothCutoff ν ε x : ℂ)) s = mellin (fun x ↦ (ν x : ℂ)) (ε * s) / s :=
  mellin_smoothCutoff hε hs
    (mellinConvergent_of_support_subset_of_integrableOn_div (by norm_num) hνs
      (integrable_of_integral_eq_one hνm) _)

example {ν : ℝ → ℝ} {k : ℕ} (hν : ContDiff ℝ k ν) (hνs : Function.support ν ⊆ Icc (1 / 2) 2)
    {σ₁ σ₂ : ℝ} (hσ₁ : 0 < σ₁) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
      ‖mellin (fun x ↦ (smoothCutoff ν ε x : ℂ)) s‖ ≤ C / (‖s‖ * (1 + ε * ‖s‖) ^ k) :=
  let ⟨C, _, hC⟩ := norm_mellin_smoothCutoff_le (by norm_num) hν hνs σ₂
  ⟨C, fun ε hε hε1 s h1 h2 ↦ hC ε hε hε1 s (hσ₁.trans_le h1) h2⟩

end TauCeti
