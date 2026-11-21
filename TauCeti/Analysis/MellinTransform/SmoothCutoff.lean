/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MellinTransform
import TauCeti.Analysis.MellinTransform
import TauCeti.Analysis.MellinTransform.Basic
import TauCeti.Analysis.MellinTransform.Convolution
import TauCeti.Analysis.MellinTransform.Decay
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds

/-!
# Delta spikes and smoothed cutoffs for the measure `dx/x`

A *bump* is a function `ν : ℝ → ℝ` with `ν ≥ 0`, support in `[1/2, 2]` and
`∫_{(0,∞)} ν(x) dx/x = 1`. For `ε > 0` its *delta spike* is `ν_ε(x) = ε⁻¹ ν(x^{1/ε})` for
`x > 0` (and `0` for `x ≤ 0`): a bump supported in `[2^{-ε}, 2^ε]`, of `dx/x`-mass `1`, whose
Mellin transform at `s` is `mellin ν (εs)`. As `ε → 0⁺` the spikes concentrate at `1`.

The *smoothed cutoff* `χ_ε(x) = ∫_{(x,∞)} ν_ε(z) dz/z` (for `x > 0`, and `0` for `x ≤ 0`) is
the Mellin convolution of the sharp cutoff `1_(0,1]` with `ν_ε`. It takes values in `[0, 1]`,
equals `1` on `(0, 2^{-ε}]` and `0` on `[2^ε, ∞)`, and its Mellin transform is
`mellin ν (εs) / s` on `Re s > 0`: the transform `1/s` of the sharp cutoff, times the factor
`mellin ν (εs)`, whose value `mellin ν ε` at `s = 1` is within `2 log 2 · ε` of `mellin ν 0 = 1`.
For `ν` of class `C^k` the transform decays like `|s|⁻¹ (1 + ε|s|)⁻ᵏ` on vertical strips,
uniformly in `ε ∈ (0, 1]`. For a `C¹` bump, weighting a sum `Σ a(n)` by `χ_ε(n/X)` therefore
gives a smoothed summatory function whose Mellin–Perron integral converges absolutely, which is
how such sums are compared with zero-free regions of their Dirichlet series.

## Main definitions

* `TauCeti.deltaSpike ν ε`: the delta spike `ν_ε`.
* `TauCeti.smoothCutoff ν ε`: the smoothed cutoff `χ_ε`.

## Main results

* `TauCeti.support_deltaSpike_subset`, `TauCeti.integral_deltaSpike_div`: the spike is supported
  in `[2^{-ε}, 2^ε]` and has the same `dx/x`-mass as `ν`.
* `TauCeti.mellin_deltaSpike`: `mellin ν_ε s = mellin ν (εs)`.
* `TauCeti.norm_mellin_sub_one_le`: `‖mellin ν ε - 1‖ ≤ 2 log 2 · ε` for a bump and `0 ≤ ε ≤ 1`.
* `TauCeti.smoothCutoff_eq_one`, `TauCeti.smoothCutoff_eq_zero`, `TauCeti.smoothCutoff_nonneg`,
  `TauCeti.smoothCutoff_le_one`: the shape of the cutoff.
* `TauCeti.smoothCutoff_eq_integral_mul_div`: the cutoff as the Mellin convolution
  `1_(0,1] ⋆ ν_ε`.
* `TauCeti.continuousOn_smoothCutoff`: the cutoff is continuous on `(0, ∞)`.
* `TauCeti.mellin_smoothCutoff`, `TauCeti.hasMellin_smoothCutoff`:
  `mellin χ_ε s = mellin ν (εs) / s` for `Re s > 0`, with absolute convergence.
* `TauCeti.exists_norm_mellin_smoothCutoff_le`: `‖mellin χ_ε s‖ ≤ C / (|s| (1 + ε|s|)^k)` on a
  vertical strip, uniformly in `0 < ε ≤ 1`.
* `TauCeti.norm_mellin_smoothCutoff_one_sub_one_le`: `‖mellin χ_ε 1 - 1‖ ≤ 2 log 2 · ε`.

## References

* A. Kontorovich, T. Tao et al., *PrimeNumberTheoremAnd* blueprint, §4.3 (Definitions 4.3.2 and
  4.3.3, Lemmas 4.3.3–4.3.11), <https://github.com/AlexKontorovich/PrimeNumberTheoremAnd>.
-/

public section

open Set MeasureTheory Complex Filter

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

theorem deltaSpike_nonneg (hν : ∀ x, 0 ≤ ν x) (hε : 0 ≤ ε) (x : ℝ) : 0 ≤ deltaSpike ν ε x := by
  unfold deltaSpike
  split_ifs
  · exact mul_nonneg (inv_nonneg.mpr hε) (hν _)
  · exact le_rfl

/-- The spike of a function supported in `[1/2, 2]` is supported in `[2^{-ε}, 2^ε]`. -/
theorem support_deltaSpike_subset (hνs : Function.support ν ⊆ Icc (1 / 2) 2) (hε : 0 < ε) :
    Function.support (deltaSpike ν ε) ⊆ Icc (2 ^ (-ε)) (2 ^ ε) := by
  intro x hx
  have hx0 : 0 < x := by
    by_contra h
    exact hx (deltaSpike_of_nonpos (not_lt.mp h))
  rw [Function.mem_support, deltaSpike_of_pos hx0] at hx
  obtain ⟨h1, h2⟩ := hνs (right_ne_zero_of_mul hx)
  have hxe : (x ^ ε⁻¹) ^ ε = x := Real.rpow_inv_rpow hx0.le hε.ne'
  constructor
  · calc (2 : ℝ) ^ (-ε) = (1 / 2) ^ ε := by
          rw [Real.rpow_neg zero_le_two, one_div, Real.inv_rpow zero_le_two]
      _ ≤ (x ^ ε⁻¹) ^ ε := Real.rpow_le_rpow (by norm_num) h1 hε.le
      _ = x := hxe
  · calc x = (x ^ ε⁻¹) ^ ε := hxe.symm
      _ ≤ 2 ^ ε := Real.rpow_le_rpow (Real.rpow_nonneg hx0.le _) h2 hε.le

private lemma ofReal_deltaSpike_of_pos (hx : 0 < x) :
    (deltaSpike ν ε x : ℂ) = ε⁻¹ • (ν (x ^ ε⁻¹) : ℂ) := by
  simp [deltaSpike_of_pos hx, real_smul]

/-- The Mellin transform of the spike at `s` is the Mellin transform of `ν` at `εs`. No
hypothesis on `ν` is needed: both sides are the junk value `0` together. -/
theorem mellin_deltaSpike (ν : ℝ → ℝ) (hε : 0 < ε) (s : ℂ) :
    mellin (fun x ↦ (deltaSpike ν ε x : ℂ)) s = mellin (fun x ↦ (ν x : ℂ)) (ε * s) := by
  have h : mellin (fun x ↦ (deltaSpike ν ε x : ℂ)) s =
      mellin (fun x ↦ ε⁻¹ • (ν (x ^ ε⁻¹) : ℂ)) s :=
    setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ by
      simp only [ofReal_deltaSpike_of_pos (mem_Ioi.mp hx)]
  rw [h, mellin_const_smul, mellin_comp_rpow (fun y ↦ (ν y : ℂ))]
  simp [abs_of_pos hε, hε.ne', mul_comm]

/-- The spike is Mellin convergent at `s` exactly when `ν` is Mellin convergent at `εs`. -/
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

/-- The spike has the same `dx/x`-mass as `ν`; in particular the spike of a bump has
`dx/x`-mass `1`. -/
theorem integral_deltaSpike_div (ν : ℝ → ℝ) (hε : 0 < ε) :
    ∫ x in Ioi 0, deltaSpike ν ε x / x = ∫ x in Ioi 0, ν x / x := by
  have h := mellin_deltaSpike ν hε 0
  rwa [mul_zero, mellin_ofReal_zero, mellin_ofReal_zero, ofReal_inj] at h

/-- For a bump `ν` (`ν ≥ 0`, supported in `[1/2, 2]`, of `dx/x`-mass `1`) and `0 ≤ ε ≤ 1`,
`‖mellin ν ε - 1‖ ≤ 2 log 2 · ε`. This is the distance between the Mellin transform of the spike
`ν_ε` at `s = 1` and that of the sharp cutoff. -/
theorem norm_mellin_sub_one_le (hν0 : ∀ x, 0 ≤ ν x) (hνs : Function.support ν ⊆ Icc (1 / 2) 2)
    (hνm : ∫ x in Ioi 0, ν x / x = 1) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ‖mellin (fun x ↦ (ν x : ℂ)) ε - 1‖ ≤ 2 * Real.log 2 * ε := by
  have hνi : IntegrableOn (fun x ↦ ν x / x) (Ioi 0) :=
    Integrable.of_integral_ne_zero (hνm ▸ one_ne_zero)
  have hνc := mellinConvergent_ofReal_of_support_subset_Icc (by norm_num) hνs hνi
  have h1 : mellin (fun x ↦ (ν x : ℂ)) 0 = 1 := by rw [mellin_ofReal_zero, hνm, ofReal_one]
  rw [← h1, mellin, mellin, ← integral_sub (hνc _) (hνc _)]
  refine (norm_integral_le_of_norm_le (hνi.const_mul (2 * Real.log 2 * ε))
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx ↦ ?_))).trans
    (by rw [integral_const_mul, hνm, mul_one])
  have hx0 : 0 < x := hx
  by_cases hνx : ν x = 0
  · simp [hνx]
  obtain ⟨hx1, hx2⟩ := hνs hνx
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
  have hq : 0 ≤ ν x / x := div_nonneg (hν0 x) hx0.le
  rw [key, norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg hq]
  gcongr

/-! ### Smoothed cutoffs -/

/-- The smoothed cutoff `χ_ε(x) = ∫_{(x,∞)} ν_ε(z) dz/z` for `x > 0`, and `0` for `x ≤ 0`, where
`ν_ε = deltaSpike ν ε`. For `x > 0` it is the Mellin convolution of `1_(0,1]` with the spike
(`TauCeti.smoothCutoff_eq_integral_mul_div`). -/
noncomputable def smoothCutoff (ν : ℝ → ℝ) (ε x : ℝ) : ℝ :=
  if 0 < x then ∫ z in Ioi x, deltaSpike ν ε z / z else 0

theorem smoothCutoff_of_pos (hx : 0 < x) :
    smoothCutoff ν ε x = ∫ z in Ioi x, deltaSpike ν ε z / z := by
  simp [smoothCutoff, hx]

@[simp]
theorem smoothCutoff_of_nonpos (hx : x ≤ 0) : smoothCutoff ν ε x = 0 := by
  simp [smoothCutoff, hx.not_gt]

theorem smoothCutoff_nonneg (hν : ∀ x, 0 ≤ ν x) (hε : 0 ≤ ε) (x : ℝ) :
    0 ≤ smoothCutoff ν ε x := by
  unfold smoothCutoff
  split_ifs with hx
  · exact setIntegral_nonneg measurableSet_Ioi fun z hz ↦
      div_nonneg (deltaSpike_nonneg hν hε z) (hx.trans hz).le
  · exact le_rfl

/-- For a bump `ν` the smoothed cutoff is at most `1`. -/
theorem smoothCutoff_le_one (hν : ∀ x, 0 ≤ ν x) (hνm : ∫ x in Ioi 0, ν x / x = 1)
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

/-- For a bump `ν` the smoothed cutoff equals `1` on `(0, 2^{-ε}]`. -/
theorem smoothCutoff_eq_one (hνs : Function.support ν ⊆ Icc (1 / 2) 2)
    (hνm : ∫ x in Ioi 0, ν x / x = 1) (hε : 0 < ε) (hx0 : 0 < x) (hx : x ≤ 2 ^ (-ε)) :
    smoothCutoff ν ε x = 1 := by
  rw [smoothCutoff_of_pos hx0, ← hνm, ← integral_deltaSpike_div ν hε]
  refine (setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Ioi.nullMeasurableSet
    (Ioi_subset_Ioi hx0.le) ?_).symm
  filter_upwards [Measure.ae_ne volume ((2 : ℝ) ^ (-ε))] with z hz hzm
  have h0 : deltaSpike ν ε z = 0 := Function.notMem_support.mp fun h ↦
    hz (le_antisymm ((not_lt.mp hzm.2).trans hx) (support_deltaSpike_subset hνs hε h).1)
  rw [h0, zero_div]

/-- For `ν` supported in `[1/2, 2]` the smoothed cutoff vanishes on `[2^ε, ∞)`. -/
theorem smoothCutoff_eq_zero (hνs : Function.support ν ⊆ Icc (1 / 2) 2) (hε : 0 < ε)
    (hx : 2 ^ ε ≤ x) : smoothCutoff ν ε x = 0 := by
  rw [smoothCutoff_of_pos ((Real.rpow_pos_of_pos two_pos ε).trans_le hx)]
  refine setIntegral_eq_zero_of_forall_eq_zero fun z hz ↦ ?_
  have h0 : deltaSpike ν ε z = 0 := Function.notMem_support.mp fun h ↦
    (hx.trans_lt hz).not_ge (support_deltaSpike_subset hνs hε h).2
  rw [h0, zero_div]

/-- If `x ↦ ν x / x` is integrable on `(0, ∞)` (as for a bump) and `ε > 0`, the smoothed cutoff
is continuous on `(0, ∞)`. -/
theorem continuousOn_smoothCutoff (hνi : IntegrableOn (fun x ↦ ν x / x) (Ioi 0)) (hε : 0 < ε) :
    ContinuousOn (smoothCutoff ν ε) (Ioi 0) := by
  set G : ℝ → ℝ := fun z ↦ deltaSpike ν ε z / z
  have hG : IntegrableOn G (Ioi 0) := (mellinConvergent_ofReal_zero_iff _).mp
    ((mellinConvergent_deltaSpike_iff hε).mpr
      (by rw [mul_zero]; exact (mellinConvergent_ofReal_zero_iff ν).mpr hνi))
  have hGi : Integrable G := by
    rw [← integrableOn_univ]
    refine hG.of_forall_sdiff_eq_zero MeasurableSet.univ fun z hz ↦ ?_
    simp [G, deltaSpike_of_nonpos (not_lt.mp hz.2)]
  have heq : EqOn (fun x ↦ (∫ z in Ioi 0, G z) - ∫ z in 0..x, G z) (smoothCutoff ν ε) (Ioi 0) :=
    fun x hx ↦ by
      have h := intervalIntegral.integral_Ioi_sub_Ioi hG (le_of_lt hx)
      simp only [smoothCutoff_of_pos (mem_Ioi.mp hx), ← h, sub_sub_cancel, G]
  exact (continuous_const.sub (intervalIntegral.continuous_primitive
    (fun _ _ ↦ hGi.intervalIntegrable) 0)).continuousOn.congr heq.symm

/-- For `x > 0` the smoothed cutoff is the Mellin convolution
`(1_(0,1] ⋆ ν_ε)(x) = ∫_{(0,∞)} 1_(0,1](y) ν_ε(x/y) dy/y`, by the substitution `z = x/y`. -/
theorem smoothCutoff_eq_integral_mul_div (ν : ℝ → ℝ) (ε : ℝ) (hx : 0 < x) :
    (smoothCutoff ν ε x : ℂ) = ∫ y in Ioi 0,
      (Ioc 0 1).indicator (fun _ ↦ (1 : ℂ)) y * (deltaSpike ν ε (x / y) : ℂ) / y := by
  set g : ℝ → ℂ := fun z ↦ (deltaSpike ν ε z : ℂ)
  have hcongr : (∫ y in Ioi 0,
      (Ioc 0 1).indicator (fun _ ↦ (1 : ℂ)) y * (deltaSpike ν ε (x / y) : ℂ) / y) =
      mellin (fun y ↦ (Ici x).indicator g (x * y⁻¹)) 0 := by
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_
    have hy0 : 0 < y := hy
    have hiff : x ≤ x * y⁻¹ ↔ y ≤ 1 := by
      rw [← div_eq_mul_inv, le_div_iff₀ hy0, mul_le_iff_le_one_right hx]
    by_cases hy1 : y ≤ 1
    · simp [indicator, hy0, hy1, hiff.mpr hy1, g, cpow_neg_one, div_eq_mul_inv, mul_comm]
    · simp [indicator, hy1, mt hiff.mp hy1]
  rw [hcongr, mellin_comp_inv (fun u ↦ (Ici x).indicator g (x * u)),
    mellin_comp_mul_left _ _ hx, mellin_indicator_Ici g hx.le, smoothCutoff_of_pos hx,
    ← integral_complex_ofReal]
  simp only [neg_zero, cpow_zero, one_smul]
  refine setIntegral_congr_fun measurableSet_Ioi fun z _ ↦ ?_
  simp [g, cpow_neg_one, div_eq_inv_mul]

/-- For `ν` supported in `[1/2, 2]` with `x ↦ ν x / x` integrable on `(0, ∞)` (which a bump's
mass condition forces), `ε > 0` and `Re s > 0`, the smoothed cutoff is Mellin convergent at `s`
with transform `mellin ν (εs) / s`. -/
theorem hasMellin_smoothCutoff (hνs : Function.support ν ⊆ Icc (1 / 2) 2)
    (hνi : IntegrableOn (fun x ↦ ν x / x) (Ioi 0)) (hε : 0 < ε) {s : ℂ} (hs : 0 < s.re) :
    HasMellin (fun x ↦ (smoothCutoff ν ε x : ℂ)) s (mellin (fun x ↦ (ν x : ℂ)) (ε * s) / s) := by
  have h1 := hasMellin_one_Ioc hs
  have h := hasMellin_integral_mul_div h1.1
    ((mellinConvergent_deltaSpike_iff hε).mpr
      (mellinConvergent_ofReal_of_support_subset_Icc (by norm_num) hνs hνi _))
  rw [h1.2, mellin_deltaSpike ν hε, one_div_mul_eq_div] at h
  exact (hasMellin_congr fun x hx ↦ smoothCutoff_eq_integral_mul_div ν ε hx).mpr h

/-- For `ν` supported in `[1/2, 2]` with `x ↦ ν x / x` integrable on `(0, ∞)`, `ε > 0` and
`Re s > 0`, the Mellin transform of the smoothed cutoff is `mellin χ_ε s = mellin ν (εs) / s`. -/
theorem mellin_smoothCutoff (hνs : Function.support ν ⊆ Icc (1 / 2) 2)
    (hνi : IntegrableOn (fun x ↦ ν x / x) (Ioi 0)) (hε : 0 < ε) {s : ℂ} (hs : 0 < s.re) :
    mellin (fun x ↦ (smoothCutoff ν ε x : ℂ)) s = mellin (fun x ↦ (ν x : ℂ)) (ε * s) / s :=
  (hasMellin_smoothCutoff hνs hνi hε hs).2

/-- For `ν` of class `C^k` on `(0, ∞)` and supported in `[1/2, 2]`, and `0 < σ₁`, there is one
constant `C` with `‖mellin χ_ε s‖ ≤ C / (|s| (1 + ε|s|)^k)` for every `0 < ε ≤ 1` and every
`s` with `σ₁ ≤ Re s ≤ σ₂`: the decay of order `k` of `mellin ν` on vertical strips, read at
`εs`, uniformly in the smoothing parameter. -/
theorem exists_norm_mellin_smoothCutoff_le {k : ℕ} (hν : ContDiffOn ℝ k ν (Ioi 0))
    (hνs : Function.support ν ⊆ Icc (1 / 2) 2) {σ₁ σ₂ : ℝ} (hσ₁ : 0 < σ₁) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
      ‖mellin (fun x ↦ (smoothCutoff ν ε x : ℂ)) s‖ ≤ C / (‖s‖ * (1 + ε * ‖s‖) ^ k) := by
  have hpos : ∀ x ∈ Icc (1 / 2 : ℝ) 2, 0 < x := fun x hx ↦ lt_of_lt_of_le (by norm_num) hx.1
  have hνc : ContinuousOn ν (Icc (1 / 2) 2) := hν.continuousOn.mono fun x hx ↦ hpos x hx
  have hνi : IntegrableOn (fun x ↦ ν x / x) (Ioi 0) := by
    refine ((hνc.div continuousOn_id fun x hx ↦ (hpos x hx).ne').integrableOn_compact
      isCompact_Icc).of_forall_sdiff_eq_zero measurableSet_Ioi fun x hx ↦ ?_
    have h0 : ν x = 0 := Function.notMem_support.mp fun h ↦ hx.2 (hνs h)
    rw [Pi.div_apply, h0, zero_div]
  have hc : IsCompact (tsupport (fun x ↦ (ν x : ℂ)) ∩ Ioi 0) := by
    have hts : tsupport (fun x ↦ (ν x : ℂ)) ⊆ Icc (1 / 2) 2 :=
      closure_minimal (by simpa [Function.support] using hνs) isClosed_Icc
    rw [inter_eq_left.mpr (hts.trans fun x hx ↦ hpos x hx)]
    exact isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hts
  obtain ⟨C, -, hC⟩ := exists_one_add_abs_im_pow_mul_norm_mellin_le
    (ofRealCLM.contDiff.comp_contDiffOn hν) hc (isCompact_Icc (a := 0) (b := σ₂))
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

/-- For a bump `ν` and `0 < ε ≤ 1`, the Mellin transform of the smoothed cutoff at `1` is within
`2 log 2 · ε` of `1`, the transform of the sharp cutoff `1_(0,1]` there. -/
theorem norm_mellin_smoothCutoff_one_sub_one_le (hν0 : ∀ x, 0 ≤ ν x)
    (hνs : Function.support ν ⊆ Icc (1 / 2) 2) (hνm : ∫ x in Ioi 0, ν x / x = 1) (hε : 0 < ε)
    (hε1 : ε ≤ 1) :
    ‖mellin (fun x ↦ (smoothCutoff ν ε x : ℂ)) 1 - 1‖ ≤ 2 * Real.log 2 * ε := by
  rw [mellin_smoothCutoff hνs (Integrable.of_integral_ne_zero (hνm ▸ one_ne_zero)) hε
    (by norm_num : (0 : ℝ) < (1 : ℂ).re), mul_one, div_one]
  exact norm_mellin_sub_one_le hν0 hνs hνm hε.le hε1

end TauCeti
