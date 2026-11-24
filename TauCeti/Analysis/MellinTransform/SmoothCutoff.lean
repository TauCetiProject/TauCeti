/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.MellinTransform.CutoffKernel
import TauCeti.Analysis.MellinTransform.Decay
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds
import TauCeti.MeasureTheory.Measure.Haar.MultHaar

/-!
# Delta spikes and smoothed cutoffs for the measure `dx/x`

A *bump* is a function `ν : ℝ → ℝ` with `ν ≥ 0` on `(0, ∞)`, vanishing on `(0, ∞)` off
`[1/2, 2]`, and with `∫_{(0,∞)} ν(x) dx/x = 1`; its values on `(-∞, 0]` never enter. For `ε > 0`
its *delta spike* is `ν_ε(x) = ε⁻¹ ν(x^{1/ε})` for `x > 0` (and `0` for `x ≤ 0`): a function
supported in `[2^{-ε}, 2^ε]`, of `dx/x`-mass `1`, whose Mellin transform at `s` is
`mellin ν (εs)`.

As `ε → 0⁺` the spikes concentrate at `1`, and Mellin convolution with them is an approximate
identity for `dx/x`. Let `ν ≥ 0` on `(0, ∞)` have `dx/x`-mass `1` and vanish on `(0, ∞)` off
`[a, b]` with `0 < a`. If `f` is a.e. strongly measurable on `(0, ∞)` and continuous at `x > 0`,
the convolution of `ν_ε` with `f` tends to `f x` at `x`; if `f` is continuous on `(0, ∞)`, the
convergence is uniform on compact subsets of `(0, ∞)`. Both follow from a quantitative bound: for
`ε > 0`, `x > 0`, `ε max(|log a|, |log b|) < R` and `f` a.e. strongly measurable on `(0, ∞)`
with `‖f(x/y) - f(x)‖ ≤ M` whenever `y > 0` and `|log y| < R`, the convolution is within `M` of
`f x` at `x`. This bound is Mathlib's `MeasureTheory.dist_convolution_le` in the coordinates
`x = e^{-u}`.

The *smoothed cutoff* `χ_ε(x) = ∫_{(x,∞)} ν_ε(z) dz/z` (for `x > 0`, and `0` for `x ≤ 0`) is,
for `x > 0`, the Mellin convolution of the sharp cutoff `1_(0,1]` with `ν_ε`. For a bump `ν` and
`ε > 0` it takes values in `[0, 1]`, equals `1` on `(0, 2^{-ε}]` and `0` on `[2^ε, ∞)`, is
antitone on `(0, ∞)`, and takes the value `1/2` at `1` when also `ν(1/x) = ν(x)` for `x > 0`.
Its Mellin transform is `mellin ν (εs) / s` on `Re s > 0`: the transform `1/s` of the sharp
cutoff, times the factor `mellin ν (εs)`, whose value `mellin ν ε` at `s = 1` is within
`2 log 2 · ε` of `mellin ν 0 = 1` for `0 < ε ≤ 1`. For `ν` of class `C^k` on `(0, ∞)` and
vanishing there off `[1/2, 2]`, the transform decays like `|s|⁻¹ (1 + ε|s|)⁻ᵏ` on vertical strips
`σ₁ ≤ Re s ≤ σ₂` with `σ₁ > 0`, uniformly in `ε ∈ (0, 1]`. For a `C¹` bump, weighting a sum
`Σ a(n)` by `χ_ε(n/X)` therefore gives a smoothed summatory function whose Mellin–Perron integral
converges absolutely, which is how such sums are compared with zero-free regions of their
Dirichlet series.

## Main definitions

* `TauCeti.deltaSpike ν ε`: the delta spike `ν_ε`.
* `TauCeti.smoothCutoff ν ε`: the smoothed cutoff `χ_ε`.

## Main results

* `TauCeti.support_deltaSpike_subset`: for `ε > 0` and `ν` vanishing on `(0, ∞)` off `[a, b]`
  with `0 ≤ a`, the spike is supported in `[a^ε, b^ε]`.
* `TauCeti.integral_deltaSpike_div`: for `ε > 0` the spike has the same `dx/x`-mass as `ν`.
* `TauCeti.mellin_deltaSpike`: `mellin ν_ε s = mellin ν (εs)` for `ε > 0`.
* `TauCeti.norm_mellin_sub_one_le`: `‖mellin ν ε - 1‖ ≤ 2 log 2 · ε` for a bump and `0 ≤ ε ≤ 1`.
* `TauCeti.norm_mellinConv_deltaSpike_sub_le`, `TauCeti.tendsto_mellinConv_deltaSpike`,
  `TauCeti.tendstoUniformlyOn_mellinConv_deltaSpike`: the approximate identity, quantitatively,
  pointwise, and uniformly on compact subsets of `(0, ∞)`, under the hypotheses above.
* `TauCeti.smoothCutoff_nonneg` (`ν ≥ 0` on `(0, ∞)`, `ε ≥ 0`), `TauCeti.smoothCutoff_le_one`
  (`ν ≥ 0` on `(0, ∞)`, unit mass, `ε > 0`), `TauCeti.smoothCutoff_eq_one` (unit mass, support
  on `(0, ∞)` in `[1/2, 2]`, `ε > 0`), `TauCeti.smoothCutoff_eq_zero` (support on `(0, ∞)` in
  `[1/2, 2]`, `ε > 0`), `TauCeti.smoothCutoff_antitoneOn` (`ν ≥ 0` on `(0, ∞)`,
  `x ↦ ν x / x` integrable on `(0, ∞)`, `ε > 0`): the shape of the cutoff.
* `TauCeti.smoothCutoff_one_eq_half_of_symm`: the value `1/2` at `1` for `ε > 0` and `ν` of unit
  mass invariant under `x ↦ x⁻¹` on `(0, ∞)`.
* `TauCeti.smoothCutoff_eq_mellinCutoffKernel`, `TauCeti.smoothCutoff_eq_mellinConv`: for `x > 0`
  the cutoff is the Mellin cutoff kernel `TauCeti.mellinCutoffKernel` of the spike, and the Mellin
  convolution `TauCeti.mellinConv` of `1_(0,1]` with `ν_ε`.
* `TauCeti.continuousOn_smoothCutoff`: for `ε > 0` and `x ↦ ν x / x` integrable on `(0, ∞)`,
  the cutoff is continuous on `(0, ∞)`.
* `TauCeti.mellin_smoothCutoff`, `TauCeti.hasMellin_smoothCutoff`: for `ν` vanishing on `(0, ∞)`
  off `[1/2, 2]` with `x ↦ ν x / x` integrable on `(0, ∞)`, `ε > 0` and `Re s > 0`,
  `mellin χ_ε s = mellin ν (εs) / s`, with absolute convergence.
* `TauCeti.exists_norm_mellin_smoothCutoff_le`: for `ν` of class `C^k` on `(0, ∞)` vanishing there
  off `[1/2, 2]` and `0 < σ₁`, `‖mellin χ_ε s‖ ≤ C / (|s| (1 + ε|s|)^k)` for
  `σ₁ ≤ Re s ≤ σ₂`, uniformly in `0 < ε ≤ 1`.
* `TauCeti.verticalIntegrable_mellin_smoothCutoff`, `TauCeti.mellinInv_mellin_smoothCutoff`: for
  `ν` of class `C¹` on `(0, ∞)` vanishing there off `[1/2, 2]`, `ε > 0` and `σ > 0`, the transform
  is integrable on the vertical line `Re s = σ`, and Mellin inversion on that line recovers the
  cutoff on `(0, ∞)`.
* `TauCeti.norm_mellin_smoothCutoff_one_sub_one_le`: `‖mellin χ_ε 1 - 1‖ ≤ 2 log 2 · ε` for a bump
  and `0 < ε ≤ 1`.

## References

* A. Kontorovich, T. Tao et al., *PrimeNumberTheoremAnd* blueprint, §4.3 (Definitions 4.3.2 and
  4.3.3, Lemmas 4.3.3–4.3.11), <https://github.com/AlexKontorovich/PrimeNumberTheoremAnd>.
-/

public section

open Set MeasureTheory Complex Filter
open scoped Topology

namespace TauCeti

/-! ### Delta spikes -/

/-- The delta spike `ν_ε(x) = ε⁻¹ ν(x^{1/ε})` of `ν` for `x > 0`, and `0` for `x ≤ 0`. The
explicit `0` on `x ≤ 0` avoids the junk values of real powers of negative numbers. -/
noncomputable def deltaSpike (ν : ℝ → ℝ) (ε x : ℝ) : ℝ :=
  if 0 < x then ε⁻¹ * ν (x ^ ε⁻¹) else 0

variable {ν : ℝ → ℝ} {ε x : ℝ}

@[simp]
theorem deltaSpike_of_pos (hx : 0 < x) : deltaSpike ν ε x = ε⁻¹ * ν (x ^ ε⁻¹) := by
  simp [deltaSpike, hx]

@[simp]
theorem deltaSpike_of_nonpos (hx : x ≤ 0) : deltaSpike ν ε x = 0 := by
  simp [deltaSpike, hx.not_gt]

/-- At `ε = 1` the spike is `ν` itself on `(0, ∞)`. -/
theorem deltaSpike_one_of_pos (hx : 0 < x) : deltaSpike ν 1 x = ν x := by
  simp [hx]

/-- If `ν ≥ 0` on `(0, ∞)` and `ε ≥ 0`, the spike is nonnegative. -/
theorem deltaSpike_nonneg (hν : ∀ x > 0, 0 ≤ ν x) (hε : 0 ≤ ε) (x : ℝ) :
    0 ≤ deltaSpike ν ε x := by
  unfold deltaSpike
  split_ifs with hx
  · exact mul_nonneg (inv_nonneg.mpr hε) (hν _ (Real.rpow_pos_of_pos hx _))
  · exact le_rfl

/-- At scale `ε = 0` the spike is identically zero, because `0⁻¹ = 0` in `ℝ`. -/
@[simp]
theorem deltaSpike_scale_zero (ν : ℝ → ℝ) (x : ℝ) : deltaSpike ν 0 x = 0 := by
  simp [deltaSpike]

/-- The spike of a function invariant under `x ↦ x⁻¹` on `(0, ∞)` is invariant under it too. -/
theorem deltaSpike_inv_of_symm (hsym : ∀ x > 0, ν x⁻¹ = ν x) (hx : 0 < x) :
    deltaSpike ν ε x⁻¹ = deltaSpike ν ε x := by
  rw [deltaSpike_of_pos (inv_pos.mpr hx), deltaSpike_of_pos hx, Real.inv_rpow hx.le,
    hsym _ (Real.rpow_pos_of_pos hx _)]

/-- If `ν` vanishes on `(0, ∞)` off `[a, b]` with `0 ≤ a`, then for `ε > 0` its spike is supported
in `[a^ε, b^ε]`. -/
theorem support_deltaSpike_subset {a b : ℝ} (ha : 0 ≤ a)
    (hνs : Function.support ν ∩ Ioi 0 ⊆ Icc a b) (hε : 0 < ε) :
    Function.support (deltaSpike ν ε) ⊆ Icc (a ^ ε) (b ^ ε) := by
  intro x hx
  have hx0 : 0 < x := by
    by_contra h
    exact hx (deltaSpike_of_nonpos (not_lt.mp h))
  rw [Function.mem_support, deltaSpike_of_pos hx0] at hx
  obtain ⟨h1, h2⟩ := hνs ⟨right_ne_zero_of_mul hx, Real.rpow_pos_of_pos hx0 _⟩
  have hxe : (x ^ ε⁻¹) ^ ε = x := Real.rpow_inv_rpow hx0.le hε.ne'
  constructor
  · calc a ^ ε ≤ (x ^ ε⁻¹) ^ ε := Real.rpow_le_rpow ha h1 hε.le
      _ = x := hxe
  · calc x = (x ^ ε⁻¹) ^ ε := hxe.symm
      _ ≤ b ^ ε := Real.rpow_le_rpow (Real.rpow_nonneg hx0.le _) h2 hε.le

/-- For `ε > 0`, the spike of a function vanishing on `(0, ∞)` off `[1/2, 2]` is supported in
`[2^{-ε}, 2^ε]`. -/
private lemma support_deltaSpike_subset_two
    (hνs : Function.support ν ∩ Ioi 0 ⊆ Icc (1 / 2) 2) (hε : 0 < ε) :
    Function.support (deltaSpike ν ε) ⊆ Icc (2 ^ (-ε)) (2 ^ ε) := by
  have h := support_deltaSpike_subset (by norm_num) hνs hε
  rwa [one_div, Real.inv_rpow zero_le_two, ← Real.rpow_neg zero_le_two] at h

private lemma ofReal_deltaSpike_of_pos (hx : 0 < x) :
    (deltaSpike ν ε x : ℂ) = ε⁻¹ • (ν (x ^ ε⁻¹) : ℂ) := by
  simp [deltaSpike_of_pos hx, real_smul]

/-- For `ε > 0` the Mellin transform of the spike at `s` is the Mellin transform of `ν` at `εs`. No
hypothesis on `ν` is needed: both sides are the junk value `0` together. -/
theorem mellin_deltaSpike (ν : ℝ → ℝ) (hε : 0 < ε) (s : ℂ) :
    mellin (fun x ↦ (deltaSpike ν ε x : ℂ)) s = mellin (fun x ↦ (ν x : ℂ)) (ε * s) := by
  have h : mellin (fun x ↦ (deltaSpike ν ε x : ℂ)) s =
      mellin (fun x ↦ ε⁻¹ • (ν (x ^ ε⁻¹) : ℂ)) s :=
    setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ by
      simp only [ofReal_deltaSpike_of_pos (mem_Ioi.mp hx)]
  rw [h, mellin_const_smul, mellin_comp_rpow (fun y ↦ (ν y : ℂ))]
  simp [abs_of_pos hε, hε.ne', mul_comm]

/-- For `ε > 0` the spike is Mellin convergent at `s` exactly when `ν` is Mellin convergent at
`εs`. -/
theorem mellinConvergent_deltaSpike_iff (hε : 0 < ε) {s : ℂ} :
    MellinConvergent (fun x ↦ (deltaSpike ν ε x : ℂ)) s ↔
      MellinConvergent (fun x ↦ (ν x : ℂ)) (ε * s) := by
  have hc : MellinConvergent (fun x ↦ (deltaSpike ν ε x : ℂ)) s ↔
      MellinConvergent (fun x ↦ (ν (x ^ ε⁻¹) : ℂ)) s := by
    simp only [MellinConvergent]
    rw [integrableOn_congr_fun (fun x hx ↦ by rw [ofReal_deltaSpike_of_pos hx])
      measurableSet_Ioi]
    simp only [smul_comm _ (ε⁻¹ : ℝ)]
    exact integrable_smul_iff (inv_ne_zero hε.ne') _
  rw [hc, MellinConvergent.comp_rpow (f := fun y ↦ (ν y : ℂ)) (inv_ne_zero hε.ne'), ofReal_inv,
    div_inv_eq_mul, mul_comm]

/-- For `ε > 0` the spike has the same `dx/x`-mass as `ν`; in particular the spike of a bump has
`dx/x`-mass `1`. -/
theorem integral_deltaSpike_div (ν : ℝ → ℝ) (hε : 0 < ε) :
    ∫ x in Ioi 0, deltaSpike ν ε x / x = ∫ x in Ioi 0, ν x / x := by
  have h := mellin_deltaSpike ν hε 0
  rwa [mul_zero, mellin_ofReal_zero, mellin_ofReal_zero, ofReal_inj] at h

/-- For `ε > 0` the spike has integrable `dx/x`-density exactly when `ν` does. -/
theorem integrableOn_deltaSpike_div_iff (hε : 0 < ε) :
    IntegrableOn (fun x ↦ deltaSpike ν ε x / x) (Ioi 0) ↔
      IntegrableOn (fun x ↦ ν x / x) (Ioi 0) := by
  rw [← mellinConvergent_ofReal_zero_iff, ← mellinConvergent_ofReal_zero_iff,
    mellinConvergent_deltaSpike_iff hε, mul_zero]

/-- For a bump `ν` (`ν ≥ 0` on `(0, ∞)`, vanishing on `(0, ∞)` off `[1/2, 2]`, of `dx/x`-mass
`1`) and `0 ≤ ε ≤ 1`, `‖mellin ν ε - 1‖ ≤ 2 log 2 · ε`. This is the distance between the Mellin
transform of the spike `ν_ε` at `s = 1` and that of the sharp cutoff. -/
theorem norm_mellin_sub_one_le (hν0 : ∀ x > 0, 0 ≤ ν x)
    (hνs : Function.support ν ∩ Ioi 0 ⊆ Icc (1 / 2) 2) (hνm : ∫ x in Ioi 0, ν x / x = 1)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ‖mellin (fun x ↦ (ν x : ℂ)) ε - 1‖ ≤ 2 * Real.log 2 * ε := by
  have hνi : IntegrableOn (fun x ↦ ν x / x) (Ioi 0) :=
    Integrable.of_integral_ne_zero (hνm ▸ one_ne_zero)
  have hνc := mellinConvergent_ofReal_of_support_inter_Ioi_subset_Icc (by norm_num) hνs hνi
  have h1 : mellin (fun x ↦ (ν x : ℂ)) 0 = 1 := by rw [mellin_ofReal_zero, hνm, ofReal_one]
  rw [← h1, mellin, mellin, ← integral_sub (hνc _) (hνc _)]
  refine (norm_integral_le_of_norm_le (hνi.const_mul (2 * Real.log 2 * ε))
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx ↦ ?_))).trans
    (by rw [integral_const_mul, hνm, mul_one])
  have hx0 : 0 < x := hx
  by_cases hνx : ν x = 0
  · simp [hνx]
  obtain ⟨hx1, hx2⟩ := hνs ⟨hνx, hx0⟩
  have hlog : |Real.log x| ≤ Real.log 2 := by
    have h := Real.log_le_log (by norm_num) hx1
    rw [one_div, Real.log_inv] at h
    exact abs_le.mpr ⟨h, Real.log_le_log hx0 hx2⟩
  have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (zero_lt_two' ℝ)]
  have hle : |Real.log x * ε| ≤ Real.log 2 * ε := by
    rw [abs_mul, abs_of_nonneg hε0]
    gcongr
  have hpow : |x ^ ε - 1| ≤ 2 * Real.log 2 * ε := by
    have h := Real.abs_rpow_sub_one_le hx0 (hle.trans (by nlinarith))
    linarith
  have key : (x : ℂ) ^ ((ε : ℂ) - 1) • (ν x : ℂ) - (x : ℂ) ^ ((0 : ℂ) - 1) • (ν x : ℂ) =
      (((x ^ ε - 1) * (ν x / x) : ℝ) : ℂ) := by
    rw [← ofReal_one, ← ofReal_sub, ← ofReal_cpow hx0.le, Real.rpow_sub_one hx0.ne']
    simp [cpow_neg_one]
    ring
  have hq : 0 ≤ ν x / x := div_nonneg (hν0 x hx0) hx0.le
  rw [key, norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg hq]
  gcongr

/-! ### The approximate identity for `dx/x` -/

/-- A function of `dx/x`-mass `1` vanishing on `(0, ∞)` off `[a, b]` has `0 < b`. -/
private lemma pos_of_support_inter_Ioi_subset_Icc {a b : ℝ}
    (hνs : Function.support ν ∩ Ioi 0 ⊆ Icc a b) (hνm : ∫ x in Ioi 0, ν x / x = 1) : 0 < b := by
  by_contra hb
  refine one_ne_zero (hνm.symm.trans (setIntegral_eq_zero_of_forall_eq_zero fun x hx ↦ ?_))
  have hνx : ν x = 0 := Function.notMem_support.mp fun h ↦
    (not_lt.mp hb).not_gt ((hx : 0 < x).trans_le (hνs ⟨h, hx⟩).2)
  rw [hνx, zero_div]

/-- For every `r > 0`, `ε * max |log a| |log b| < r` for all small enough `ε > 0`. -/
private lemma eventually_mul_max_abs_log_lt (a b : ℝ) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε * max |Real.log a| |Real.log b| < r :=
  (((continuous_id.mul (continuous_const (y := max |Real.log a| |Real.log b|))).tendsto' 0 0
    (zero_mul _)).mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds hr)

/-- For `ε > 0`, in logarithmic coordinates the spike keeps the `dx/x`-mass of `ν`. -/
private lemma integral_deltaSpike_exp_neg (ν : ℝ → ℝ) (hε : 0 < ε) :
    ∫ v, deltaSpike ν ε (Real.exp (-v)) = ∫ x in Ioi 0, ν x / x := by
  have h := mellin_eq_integral_exp_smul (fun x ↦ (deltaSpike ν ε x : ℂ)) 0
  rw [mellin_deltaSpike ν hε, mul_zero, mellin_ofReal_zero] at h
  simp only [neg_zero, zero_mul, Complex.exp_zero, one_smul, integral_complex_ofReal] at h
  exact_mod_cast h.symm

/-- If `ν ≥ 0` on `(0, ∞)` vanishes there off `[a, b]` (`0 < a`) and has `dx/x`-mass `1`, `ε > 0`,
`x > 0`, `f` is a.e. strongly measurable on `(0, ∞)`, `ε * max |log a| |log b| < R` (so that the
spike is supported where `|log y| < R`), and `‖f (x / y) - f x‖ ≤ M` whenever `y > 0` and
`|log y| < R`, then the Mellin convolution of the spike with `f` is within `M` of `f x` at `x`.
This is Mathlib's `MeasureTheory.dist_convolution_le` in the coordinates `x = e^{-u}`. -/
theorem norm_mellinConv_deltaSpike_sub_le {a b : ℝ} (ha : 0 < a) (hν0 : ∀ x > 0, 0 ≤ ν x)
    (hνs : Function.support ν ∩ Ioi 0 ⊆ Icc a b) (hνm : ∫ x in Ioi 0, ν x / x = 1) {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0))) {R M : ℝ} (hε : 0 < ε) (hx : 0 < x)
    (hR : ε * max |Real.log a| |Real.log b| < R)
    (hbd : ∀ y > 0, |Real.log y| < R → ‖f (x / y) - f x‖ ≤ M) :
    ‖mellinConv (fun y ↦ (deltaSpike ν ε y : ℂ)) f x - f x‖ ≤ M := by
  set u := -Real.log x
  have hxu : Real.exp (-u) = x := by rw [neg_neg, Real.exp_log hx]
  set φ : ℝ → ℝ := fun v ↦ deltaSpike ν ε (Real.exp (-v))
  set g : ℝ → ℂ := fun v ↦ f (Real.exp (-v))
  -- The spike in logarithmic coordinates is supported in the ball of radius `R` around `0`.
  have hφR : Function.support φ ⊆ Metric.ball 0 R := by
    intro v hv
    rw [Function.mem_support] at hv
    simp only [φ] at hv
    -- `e^{-v}` lies in the support `[a^ε, b^ε]` of the spike; take logarithms.
    have hy := support_deltaSpike_subset ha.le hνs hε (Function.mem_support.mpr hv)
    have h1 := Real.log_le_log (Real.rpow_pos_of_pos ha ε) hy.1
    have h2 := Real.log_le_log (Real.exp_pos _) hy.2
    rw [Real.log_rpow ha, Real.log_exp] at h1
    rw [Real.log_rpow (pos_of_support_inter_Ioi_subset_Icc hνs hνm), Real.log_exp] at h2
    have hA := mul_le_mul_of_nonneg_left (neg_abs_le (Real.log a)) hε.le
    have hA' := mul_le_mul_of_nonneg_left (le_max_left |Real.log a| |Real.log b|) hε.le
    have hB := mul_le_mul_of_nonneg_left (le_abs_self (Real.log b)) hε.le
    have hB' := mul_le_mul_of_nonneg_left (le_max_right |Real.log a| |Real.log b|) hε.le
    rw [mem_ball_zero_iff, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith
  have hgm : AEStronglyMeasurable g volume :=
    (hf.comp_quasiMeasurePreserving quasiMeasurePreserving_exp).comp_quasiMeasurePreserving
      (Measure.measurePreserving_neg volume).quasiMeasurePreserving
  have hM : 0 ≤ M := by
    have hR0 : 0 < R := (mul_nonneg hε.le ((abs_nonneg _).trans (le_max_left _ _))).trans_lt hR
    have h := hbd 1 one_pos (by rwa [Real.log_one, abs_zero])
    rwa [div_one, sub_self, norm_zero] at h
  -- On the ball, `g w = f (x / y)` with `log y = w - u`.
  have hg : ∀ w ∈ Metric.ball u R, dist (g w) (f x) ≤ M := fun w hw ↦ by
    have h := hbd (Real.exp (w - u)) (Real.exp_pos _)
      (by rwa [Real.log_exp, ← Real.dist_eq])
    have hcoord : x / Real.exp (w - u) = Real.exp (-w) := by
      rw [← hxu, ← Real.exp_sub]
      ring_nf
    rw [hcoord] at h
    simpa only [g, dist_eq_norm] using h
  have hconv := dist_convolution_le (μ := volume) hM hφR (fun v ↦ deltaSpike_nonneg hν0 hε.le _)
    ((integral_deltaSpike_exp_neg ν hε).trans hνm) hgm hg
  rw [← dist_eq_norm, ← hxu, mellinConv_exp_neg_eq_convolution, hxu]
  convert hconv using 2
  simp only [convolution_def, ContinuousLinearMap.mul_apply', ContinuousLinearMap.lsmul_apply,
    Complex.real_smul, φ, g]

/-- **Approximate identity for `dx/x`, pointwise.** If `ν ≥ 0` on `(0, ∞)` vanishes there off
`[a, b]` (`0 < a`) and has `dx/x`-mass `1`, and `f` is a.e. strongly measurable on `(0, ∞)` and
continuous at `x > 0`, then the Mellin convolution of the spike `ν_ε` with `f` tends to `f x` at
`x` as `ε → 0⁺`. -/
theorem tendsto_mellinConv_deltaSpike {a b : ℝ} (ha : 0 < a) (hν0 : ∀ x > 0, 0 ≤ ν x)
    (hνs : Function.support ν ∩ Ioi 0 ⊆ Icc a b) (hνm : ∫ x in Ioi 0, ν x / x = 1) {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0))) (hx : 0 < x)
    (hcont : ContinuousAt f x) :
    Tendsto (fun ε ↦ mellinConv (fun y ↦ (deltaSpike ν ε y : ℂ)) f x) (𝓝[>] 0) (𝓝 (f x)) := by
  have hc : ContinuousAt (fun t ↦ f (x / Real.exp t)) 0 := by
    have h : ContinuousAt f (x / Real.exp 0) := by rwa [Real.exp_zero, div_one]
    have hdiv : ContinuousAt (fun t : ℝ ↦ x / Real.exp t) 0 :=
      continuousAt_const.div Real.continuous_exp.continuousAt (Real.exp_ne_zero 0)
    exact h.comp_of_eq hdiv rfl
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨R, hR, hRf⟩ := Metric.continuousAt_iff.mp hc (η / 2) (half_pos hη)
  filter_upwards [self_mem_nhdsWithin, eventually_mul_max_abs_log_lt a b hR] with ε hε hεR
  rw [dist_eq_norm]
  refine (norm_mellinConv_deltaSpike_sub_le ha hν0 hνs hνm hf hε hx hεR fun y hy hyR ↦ ?_).trans_lt
    (half_lt_self hη)
  have h := (hRf (by rwa [Real.dist_eq, sub_zero])).le
  rwa [Real.exp_log hy, Real.exp_zero, div_one, dist_eq_norm] at h

/-- **Approximate identity for `dx/x`, uniformly on compact sets.** If `ν ≥ 0` on `(0, ∞)`
vanishes there off `[a, b]` (`0 < a`) and has `dx/x`-mass `1`, and `f` is continuous on `(0, ∞)`,
then the Mellin convolution of the spike `ν_ε` with `f` tends to `f` uniformly on every compact
`K ⊆ (0, ∞)` as `ε → 0⁺`. -/
theorem tendstoUniformlyOn_mellinConv_deltaSpike {a b : ℝ} (ha : 0 < a)
    (hν0 : ∀ x > 0, 0 ≤ ν x) (hνs : Function.support ν ∩ Ioi 0 ⊆ Icc a b)
    (hνm : ∫ x in Ioi 0, ν x / x = 1) {f : ℝ → ℂ} (hf : ContinuousOn f (Ioi 0)) {K : Set ℝ}
    (hK : IsCompact K) (hK0 : K ⊆ Ioi 0) :
    TendstoUniformlyOn (fun ε x ↦ mellinConv (fun y ↦ (deltaSpike ν ε y : ℂ)) f x) f
      (𝓝[>] 0) K := by
  -- `(x, t) ↦ f (x / e^t)` is uniformly continuous on the compact set `K × [-1, 1]`.
  have hF : ContinuousOn (fun p : ℝ × ℝ ↦ f (p.1 / Real.exp p.2)) (K ×ˢ Icc (-1) 1) :=
    hf.comp (continuousOn_fst.div (Real.continuous_exp.comp_continuousOn continuousOn_snd)
      fun _ _ ↦ Real.exp_ne_zero _) fun p hp ↦ div_pos (hK0 hp.1) (Real.exp_pos _)
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuousOn_iff.mp
    ((hK.prod isCompact_Icc).uniformContinuousOn_of_continuous hF) (η / 2) (half_pos hη)
  filter_upwards [self_mem_nhdsWithin, eventually_mul_max_abs_log_lt a b (lt_min hδ one_pos)]
    with ε hε hεR x hxK
  rw [dist_comm, dist_eq_norm]
  refine (norm_mellinConv_deltaSpike_sub_le ha hν0 hνs hνm
    (hf.aestronglyMeasurable measurableSet_Ioi) hε (hK0 hxK) hεR fun y hy hyR ↦ ?_).trans_lt
    (half_lt_self hη)
  have hyI : Real.log y ∈ Icc (-1 : ℝ) 1 :=
    abs_le.mp (hyR.trans_le (min_le_right _ _)).le
  have h := hδf (x, Real.log y) ⟨hxK, hyI⟩ (x, 0) ⟨hxK, by norm_num⟩
    (by simpa [Prod.dist_eq] using hyR.trans_le (min_le_left _ _))
  simpa [Real.exp_log hy, dist_eq_norm] using h.le

/-! ### Smoothed cutoffs -/

/-- The smoothed cutoff `χ_ε(x) = ∫_{(x,∞)} ν_ε(z) dz/z` for `x > 0`, and `0` for `x ≤ 0`, where
`ν_ε = deltaSpike ν ε`. For `x > 0` it is the Mellin convolution of `1_(0,1]` with the spike
(`TauCeti.smoothCutoff_eq_mellinConv`). -/
noncomputable def smoothCutoff (ν : ℝ → ℝ) (ε x : ℝ) : ℝ :=
  if 0 < x then ∫ z in Ioi x, deltaSpike ν ε z / z else 0

theorem smoothCutoff_of_pos (hx : 0 < x) :
    smoothCutoff ν ε x = ∫ z in Ioi x, deltaSpike ν ε z / z := by
  simp [smoothCutoff, hx]

@[simp]
theorem smoothCutoff_of_nonpos (hx : x ≤ 0) : smoothCutoff ν ε x = 0 := by
  simp [smoothCutoff, hx.not_gt]

/-- If `ν ≥ 0` on `(0, ∞)` and `ε ≥ 0`, the smoothed cutoff is nonnegative. -/
theorem smoothCutoff_nonneg (hν : ∀ x > 0, 0 ≤ ν x) (hε : 0 ≤ ε) (x : ℝ) :
    0 ≤ smoothCutoff ν ε x := by
  unfold smoothCutoff
  split_ifs with hx
  · exact setIntegral_nonneg measurableSet_Ioi fun z hz ↦
      div_nonneg (deltaSpike_nonneg hν hε z) (hx.trans hz).le
  · exact le_rfl

/-- If `ν ≥ 0` on `(0, ∞)` has `dx/x`-mass `1` and `ε > 0`, the smoothed cutoff is at most `1`. -/
theorem smoothCutoff_le_one (hν : ∀ x > 0, 0 ≤ ν x) (hνm : ∫ x in Ioi 0, ν x / x = 1)
    (hε : 0 < ε) (x : ℝ) : smoothCutoff ν ε x ≤ 1 := by
  rcases le_or_gt x 0 with hx | hx
  · rw [smoothCutoff_of_nonpos hx]
    exact zero_le_one
  have hm := integral_deltaSpike_div ν hε
  rw [hνm] at hm
  rw [smoothCutoff_of_pos hx, ← hm]
  exact setIntegral_mono_set (Integrable.of_integral_ne_zero (hm ▸ one_ne_zero))
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun z hz ↦
      div_nonneg (deltaSpike_nonneg hν hε.le z) (le_of_lt hz)))
    (Eventually.of_forall (Ioi_subset_Ioi hx.le))

/-- If `ν` vanishes on `(0, ∞)` off `[1/2, 2]` and has `dx/x`-mass `1`, then for `ε > 0` the
smoothed cutoff equals `1` on `(0, 2^{-ε}]`. -/
theorem smoothCutoff_eq_one (hνs : Function.support ν ∩ Ioi 0 ⊆ Icc (1 / 2) 2)
    (hνm : ∫ x in Ioi 0, ν x / x = 1) (hε : 0 < ε) (hx0 : 0 < x) (hx : x ≤ 2 ^ (-ε)) :
    smoothCutoff ν ε x = 1 := by
  rw [smoothCutoff_of_pos hx0, ← hνm, ← integral_deltaSpike_div ν hε]
  refine (setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Ioi.nullMeasurableSet
    (Ioi_subset_Ioi hx0.le) ?_).symm
  filter_upwards [Measure.ae_ne volume ((2 : ℝ) ^ (-ε))] with z hz hzm
  have h0 : deltaSpike ν ε z = 0 := Function.notMem_support.mp fun h ↦
    hz (le_antisymm ((not_lt.mp hzm.2).trans hx) (support_deltaSpike_subset_two hνs hε h).1)
  rw [h0, zero_div]

/-- If `ν` vanishes on `(0, ∞)` off `[1/2, 2]`, then for `ε > 0` the smoothed cutoff vanishes on
`[2^ε, ∞)`. -/
theorem smoothCutoff_eq_zero (hνs : Function.support ν ∩ Ioi 0 ⊆ Icc (1 / 2) 2)
    (hε : 0 < ε)
    (hx : 2 ^ ε ≤ x) : smoothCutoff ν ε x = 0 := by
  rw [smoothCutoff_of_pos ((Real.rpow_pos_of_pos two_pos ε).trans_le hx)]
  refine setIntegral_eq_zero_of_forall_eq_zero fun z hz ↦ ?_
  have h0 : deltaSpike ν ε z = 0 := Function.notMem_support.mp fun h ↦
    (hx.trans_lt hz).not_ge (support_deltaSpike_subset_two hνs hε h).2
  rw [h0, zero_div]

/-- At scale `ε = 0` the smoothed cutoff is identically zero, as the spike is. -/
@[simp]
theorem smoothCutoff_scale_zero (ν : ℝ → ℝ) (x : ℝ) : smoothCutoff ν 0 x = 0 := by
  simp [smoothCutoff]

/-- If `ν ≥ 0` on `(0, ∞)` with `x ↦ ν x / x` integrable there and `ε > 0`, the smoothed cutoff is
antitone on `(0, ∞)`. -/
theorem smoothCutoff_antitoneOn (hν : ∀ x > 0, 0 ≤ ν x)
    (hνi : IntegrableOn (fun x ↦ ν x / x) (Ioi 0)) (hε : 0 < ε) :
    AntitoneOn (smoothCutoff ν ε) (Ioi 0) := by
  intro x hx y hy hxy
  rw [smoothCutoff_of_pos hx, smoothCutoff_of_pos hy]
  exact setIntegral_mono_set
    (((integrableOn_deltaSpike_div_iff hε).mpr hνi).mono_set (Ioi_subset_Ioi (le_of_lt hx)))
    ((ae_restrict_mem measurableSet_Ioi).mono fun z hz ↦
      div_nonneg (deltaSpike_nonneg hν hε.le z) (hx.trans hz).le)
    (Eventually.of_forall (Ioi_subset_Ioi hxy))

/-- If `ν` is invariant under `x ↦ x⁻¹` on `(0, ∞)` and has `dx/x`-mass `1`, then for `ε > 0` the
smoothed cutoff takes the value `1/2` at `1`: the spike has the same mass on `(0, 1]` as on
`(1, ∞)`. -/
theorem smoothCutoff_one_eq_half_of_symm (hsym : ∀ x > 0, ν x⁻¹ = ν x)
    (hνm : ∫ x in Ioi 0, ν x / x = 1) (hε : 0 < ε) : smoothCutoff ν ε 1 = 1 / 2 := by
  have hint : IntegrableOn (fun z ↦ deltaSpike ν ε z / z) (Ioi 0) :=
    (integrableOn_deltaSpike_div_iff hε).mpr (Integrable.of_integral_ne_zero (hνm ▸ one_ne_zero))
  -- The total mass `1` splits as the mass on `(0, 1]` plus the mass on `(1, ∞)`.
  have hsplit := intervalIntegral.integral_interval_add_Ioi hint
    (hint.mono_set (Ioi_subset_Ioi zero_le_one))
  rw [intervalIntegral.integral_of_le zero_le_one, integral_deltaSpike_div ν hε, hνm] at hsplit
  -- Inversion `z ↦ z⁻¹` preserves `dz/z` and exchanges the two pieces.
  have hinv := mellin_comp_inv (fun z ↦ (((Ioi 1).indicator (deltaSpike ν ε) z : ℝ) : ℂ)) 0
  rw [neg_zero, mellin_ofReal_zero, mellin_ofReal_zero] at hinv
  have hright : ∫ z in Ioi 0, (Ioi 1).indicator (deltaSpike ν ε) z / z =
      ∫ z in Ioi 1, deltaSpike ν ε z / z := by
    have hcongr : ∫ z in Ioi 0, (Ioi 1).indicator (deltaSpike ν ε) z / z =
        ∫ z in Ioi 0, (Ioi 1).indicator (fun z ↦ deltaSpike ν ε z / z) z :=
      setIntegral_congr_fun measurableSet_Ioi fun z _ ↦ by by_cases hz : z ∈ Ioi 1 <;> simp [hz]
    rw [hcongr, setIntegral_indicator measurableSet_Ioi,
      inter_eq_right.mpr (Ioi_subset_Ioi zero_le_one)]
  have hleft : ∫ z in Ioi 0, (Ioi 1).indicator (deltaSpike ν ε) z⁻¹ / z =
      ∫ z in Ioc 0 1, deltaSpike ν ε z / z := by
    have hcongr : ∫ z in Ioi 0, (Ioi 1).indicator (deltaSpike ν ε) z⁻¹ / z =
        ∫ z in Ioi 0, (Ioo 0 1).indicator (fun z ↦ deltaSpike ν ε z / z) z := by
      refine setIntegral_congr_fun measurableSet_Ioi fun z (hz : 0 < z) ↦ ?_
      have hiff : z⁻¹ ∈ Ioi 1 ↔ z ∈ Ioo 0 1 := by simp [hz, one_lt_inv₀ hz]
      by_cases hz1 : z ∈ Ioo 0 1
      · rw [indicator_of_mem (hiff.mpr hz1), indicator_of_mem hz1, deltaSpike_inv_of_symm hsym hz]
      · rw [indicator_of_notMem (mt hiff.mp hz1), indicator_of_notMem hz1, zero_div]
    rw [hcongr, setIntegral_indicator measurableSet_Ioo, inter_eq_right.mpr Ioo_subset_Ioi_self,
      integral_Ioc_eq_integral_Ioo]
  rw [hleft, hright, ofReal_inj] at hinv
  rw [smoothCutoff_of_pos one_pos]
  linarith

/-- For `x > 0` the smoothed cutoff is the Mellin cutoff kernel `∫_{(x,∞)} ν_ε(z) dz/z` of the
delta spike. -/
theorem smoothCutoff_eq_mellinCutoffKernel (ν : ℝ → ℝ) (ε : ℝ) (hx : 0 < x) :
    smoothCutoff ν ε x = mellinCutoffKernel (deltaSpike ν ε) x := by
  rw [smoothCutoff_of_pos hx, mellinCutoffKernel_def]
  simp only [smul_eq_mul, inv_mul_eq_div]

/-- If `x ↦ ν x / x` is integrable on `(0, ∞)` (as for a bump) and `ε > 0`, the smoothed cutoff
is continuous on `(0, ∞)`. -/
theorem continuousOn_smoothCutoff (hνi : IntegrableOn (fun x ↦ ν x / x) (Ioi 0)) (hε : 0 < ε) :
    ContinuousOn (smoothCutoff ν ε) (Ioi 0) := by
  have hG : IntegrableOn (fun z ↦ z⁻¹ • deltaSpike ν ε z) (Ioi 0) := by
    simpa only [smul_eq_mul, inv_mul_eq_div] using (integrableOn_deltaSpike_div_iff hε).mpr hνi
  exact (hG.continuousOn_mellinCutoffKernel.mono Ioi_subset_Ici_self).congr
    fun x hx ↦ smoothCutoff_eq_mellinCutoffKernel ν ε hx

/-- For `x > 0` the smoothed cutoff is the Mellin convolution `(1_(0,1] ⋆ ν_ε)(x)`. -/
theorem smoothCutoff_eq_mellinConv (ν : ℝ → ℝ) (ε : ℝ) (hx : 0 < x) :
    (smoothCutoff ν ε x : ℂ) =
      mellinConv ((Ioc 0 1).indicator fun _ ↦ (1 : ℂ)) (fun y ↦ (deltaSpike ν ε y : ℂ)) x := by
  rw [smoothCutoff_eq_mellinCutoffKernel ν ε hx, ← mellinCutoffKernel_ofReal,
    mellinCutoffKernel_eq_mellinConv _ hx]

/-- For `ν` vanishing on `(0, ∞)` off `[1/2, 2]` with `x ↦ ν x / x` integrable on `(0, ∞)` (which
a bump's mass condition forces), `ε > 0` and `Re s > 0`, the smoothed cutoff is Mellin convergent
at `s` with transform `mellin ν (εs) / s`. -/
theorem hasMellin_smoothCutoff (hνs : Function.support ν ∩ Ioi 0 ⊆ Icc (1 / 2) 2)
    (hνi : IntegrableOn (fun x ↦ ν x / x) (Ioi 0)) (hε : 0 < ε) {s : ℂ} (hs : 0 < s.re) :
    HasMellin (fun x ↦ (smoothCutoff ν ε x : ℂ)) s (mellin (fun x ↦ (ν x : ℂ)) (ε * s) / s) := by
  have hm := (mellinConvergent_deltaSpike_iff hε (s := s)).mpr
    (mellinConvergent_ofReal_of_support_inter_Ioi_subset_Icc (by norm_num) hνs hνi _)
  have h := hm.hasMellin_mellinCutoffKernel hs
  rw [mellin_deltaSpike ν hε] at h
  exact (hasMellin_congr fun x hx ↦ by
    rw [smoothCutoff_eq_mellinCutoffKernel ν ε hx, ← mellinCutoffKernel_ofReal]).mpr h

/-- For `ν` vanishing on `(0, ∞)` off `[1/2, 2]` with `x ↦ ν x / x` integrable on `(0, ∞)`,
`ε > 0` and `Re s > 0`, the Mellin transform of the smoothed cutoff is
`mellin χ_ε s = mellin ν (εs) / s`. -/
theorem mellin_smoothCutoff (hνs : Function.support ν ∩ Ioi 0 ⊆ Icc (1 / 2) 2)
    (hνi : IntegrableOn (fun x ↦ ν x / x) (Ioi 0)) (hε : 0 < ε) {s : ℂ} (hs : 0 < s.re) :
    mellin (fun x ↦ (smoothCutoff ν ε x : ℂ)) s = mellin (fun x ↦ (ν x : ℂ)) (ε * s) / s :=
  (hasMellin_smoothCutoff hνs hνi hε hs).2

/-- A function continuous on `(0, ∞)` and vanishing there off `[1/2, 2]` has `x ↦ ν x / x`
integrable on `(0, ∞)`. -/
private lemma integrableOn_div_of_continuousOn (hν : ContinuousOn ν (Ioi 0))
    (hνs : Function.support ν ∩ Ioi 0 ⊆ Icc (1 / 2) 2) :
    IntegrableOn (fun x ↦ ν x / x) (Ioi 0) := by
  have hpos : Icc (1 / 2 : ℝ) 2 ⊆ Ioi 0 := fun x hx ↦ lt_of_lt_of_le (by norm_num) hx.1
  refine (((hν.mono hpos).div continuousOn_id fun x hx ↦ (hpos hx).ne').integrableOn_compact
    isCompact_Icc).of_forall_sdiff_eq_zero measurableSet_Ioi fun x hx ↦ ?_
  have h0 : ν x = 0 := Function.notMem_support.mp fun h ↦ hx.2 (hνs ⟨h, hx.1⟩)
  rw [Pi.div_apply, h0, zero_div]

private lemma isCompact_tsupport_ofReal_inter_Ioi
    (hνs : Function.support ν ∩ Ioi 0 ⊆ Icc (1 / 2) 2) :
    IsCompact (tsupport (fun x ↦ (ν x : ℂ)) ∩ Ioi 0) := by
  have hpos : Icc (1 / 2 : ℝ) 2 ⊆ Ioi 0 := fun x hx ↦ lt_of_lt_of_le (by norm_num) hx.1
  -- `Ioi 0` is open, so the positive closed support lies in the closure of the positive support.
  have hts : tsupport (fun x ↦ (ν x : ℂ)) ∩ Ioi 0 ⊆ Icc (1 / 2) 2 := by
    rw [inter_comm]
    refine isOpen_Ioi.inter_closure.trans (closure_minimal ?_ isClosed_Icc)
    rw [inter_comm]
    simpa [Function.support] using hνs
  have heq : tsupport (fun x ↦ (ν x : ℂ)) ∩ Ioi 0 =
      tsupport (fun x ↦ (ν x : ℂ)) ∩ Icc (1 / 2) 2 :=
    Subset.antisymm (subset_inter inter_subset_left hts) (inter_subset_inter_right _ hpos)
  rw [heq]
  exact isCompact_Icc.inter_left (isClosed_tsupport _)

/-- For `ν` of class `C^k` on `(0, ∞)` and vanishing there off `[1/2, 2]`, and `0 < σ₁`, there is
one constant `C` with `‖mellin χ_ε s‖ ≤ C / (|s| (1 + ε|s|)^k)` for every `0 < ε ≤ 1` and every
`s` with `σ₁ ≤ Re s ≤ σ₂`: the decay of order `k` of `mellin ν` on vertical strips, read at
`εs`, uniformly in the smoothing parameter. -/
theorem exists_norm_mellin_smoothCutoff_le {k : ℕ} (hν : ContDiffOn ℝ k ν (Ioi 0))
    (hνs : Function.support ν ∩ Ioi 0 ⊆ Icc (1 / 2) 2) {σ₁ σ₂ : ℝ} (hσ₁ : 0 < σ₁) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
      ‖mellin (fun x ↦ (smoothCutoff ν ε x : ℂ)) s‖ ≤ C / (‖s‖ * (1 + ε * ‖s‖) ^ k) := by
  have hνi := integrableOn_div_of_continuousOn hν.continuousOn hνs
  obtain ⟨C, -, hC⟩ := exists_one_add_abs_im_pow_mul_norm_mellin_le
    (ofRealCLM.contDiff.comp_contDiffOn hν) (isCompact_tsupport_ofReal_inter_Ioi hνs)
    (isCompact_Icc (a := 0) (b := σ₂))
  simp only [Function.comp_def, ofRealCLM_apply] at hC
  refine ⟨(1 + σ₂) ^ k * C, fun ε hε hε1 s hs1 hs2 ↦ ?_⟩
  have hs0 : 0 < s.re := hσ₁.trans_le hs1
  have hsn : 0 < ‖s‖ := hs0.trans_le (re_le_norm s)
  have hre : (ε * s : ℂ).re = ε * s.re := re_ofReal_mul ε s
  have him : (ε * s : ℂ).im = ε * s.im := im_ofReal_mul ε s
  have hw := hC (ε * s) (by
    rw [hre]
    exact ⟨mul_nonneg hε.le hs0.le, (mul_le_of_le_one_left hs0.le hε1).trans hs2⟩)
  have hle : 1 + ε * ‖s‖ ≤ (1 + σ₂) * (1 + |(ε * s : ℂ).im|) := by
    have hn : ‖s‖ ≤ s.re + |s.im| := by
      simpa [abs_of_pos hs0] using norm_le_abs_re_add_abs_im s
    rw [him, abs_mul, abs_of_pos hε]
    have h1 : ε * ‖s‖ ≤ ε * s.re + ε * |s.im| := by
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left hn hε.le
    have h2 : ε * s.re ≤ σ₂ := (mul_le_of_le_one_left hs0.le hε1).trans hs2
    have h3 : 0 ≤ σ₂ * (ε * |s.im|) :=
      mul_nonneg (hs0.le.trans hs2) (mul_nonneg hε.le (abs_nonneg _))
    linarith
  rw [mellin_smoothCutoff hνs hνi hε hs0, norm_div,
    div_le_div_iff₀ hsn (by positivity)]
  set A := ‖mellin (fun x ↦ (ν x : ℂ)) (ε * s)‖
  have hσ₂ : 0 ≤ 1 + σ₂ := by linarith
  calc A * (‖s‖ * (1 + ε * ‖s‖) ^ k) = ‖s‖ * ((1 + ε * ‖s‖) ^ k * A) := by ring
    _ ≤ ‖s‖ * (((1 + σ₂) * (1 + |(ε * s : ℂ).im|)) ^ k * A) := by gcongr
    _ = ‖s‖ * ((1 + σ₂) ^ k * ((1 + |(ε * s : ℂ).im|) ^ k * A)) := by rw [mul_pow]; ring
    _ ≤ ‖s‖ * ((1 + σ₂) ^ k * C) := by gcongr
    _ = (1 + σ₂) ^ k * C * ‖s‖ := by ring

/-- For `ν` of class `C¹` on `(0, ∞)` and vanishing there off `[1/2, 2]`, `ε > 0` and `σ > 0`,
the Mellin transform of the smoothed cutoff is integrable on the vertical line `Re s = σ`: on that
line it is `mellin ν (εs) / s = ε · mellin ν (εs) / (εs)`, the rescaling of the integrable
`mellin ν w / w` on the line `Re w = εσ`. -/
theorem verticalIntegrable_mellin_smoothCutoff (hν : ContDiffOn ℝ 1 ν (Ioi 0))
    (hνs : Function.support ν ∩ Ioi 0 ⊆ Icc (1 / 2) 2) (hε : 0 < ε) {σ : ℝ} (hσ : 0 < σ) :
    VerticalIntegrable (mellin fun x ↦ (smoothCutoff ν ε x : ℂ)) σ := by
  have hνi := integrableOn_div_of_continuousOn hν.continuousOn hνs
  have h := ((ofRealCLM.contDiff.comp_contDiffOn hν).verticalIntegrable_mellin_div
    (isCompact_tsupport_ofReal_inter_Ioi hνs) (mul_pos hε hσ).ne').comp_mul_left' hε.ne'
  simp only [Function.comp_def, ofRealCLM_apply] at h
  refine (h.const_mul ε).congr (Eventually.of_forall fun t ↦ ?_)
  have hw : (((ε * σ : ℝ) : ℂ) + ((ε * t : ℝ) : ℂ) * I) = ε * (σ + t * I) := by
    push_cast
    ring
  have hε' : (ε : ℂ) ≠ 0 := ofReal_ne_zero.mpr hε.ne'
  dsimp only
  rw [mellin_smoothCutoff hνs hνi hε (by simpa using hσ), hw, mul_div_assoc',
    mul_div_mul_left _ _ hε']

/-- **Mellin inversion for the smoothed cutoff.** For `ν` of class `C¹` on `(0, ∞)` and vanishing
there off `[1/2, 2]`, `ε > 0`, `σ > 0` and `x > 0`, the inverse Mellin integral of `mellin χ_ε`
on the line `Re s = σ` recovers `χ_ε(x)`. -/
theorem mellinInv_mellin_smoothCutoff (hν : ContDiffOn ℝ 1 ν (Ioi 0))
    (hνs : Function.support ν ∩ Ioi 0 ⊆ Icc (1 / 2) 2) (hε : 0 < ε) {σ : ℝ} (hσ : 0 < σ)
    (hx : 0 < x) :
    mellinInv σ (mellin fun x ↦ (smoothCutoff ν ε x : ℂ)) x = smoothCutoff ν ε x := by
  have hνi := integrableOn_div_of_continuousOn hν.continuousOn hνs
  exact mellinInv_mellin_eq σ _ hx (hasMellin_smoothCutoff hνs hνi hε (by simpa using hσ)).1
    (verticalIntegrable_mellin_smoothCutoff hν hνs hε hσ)
    (continuous_ofReal.continuousAt.comp ((continuousOn_smoothCutoff hνi hε).continuousAt
      (Ioi_mem_nhds hx)))

/-- For a bump `ν` and `0 < ε ≤ 1`, the Mellin transform of the smoothed cutoff at `1` is within
`2 log 2 · ε` of `1`, the transform of the sharp cutoff `1_(0,1]` there. -/
theorem norm_mellin_smoothCutoff_one_sub_one_le (hν0 : ∀ x > 0, 0 ≤ ν x)
    (hνs : Function.support ν ∩ Ioi 0 ⊆ Icc (1 / 2) 2) (hνm : ∫ x in Ioi 0, ν x / x = 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ‖mellin (fun x ↦ (smoothCutoff ν ε x : ℂ)) 1 - 1‖ ≤ 2 * Real.log 2 * ε := by
  rw [mellin_smoothCutoff hνs (Integrable.of_integral_ne_zero (hνm ▸ one_ne_zero)) hε
    (by norm_num : (0 : ℝ) < (1 : ℂ).re), mul_one, div_one]
  exact norm_mellin_sub_one_le hν0 hνs hνm hε.le hε1

end TauCeti
