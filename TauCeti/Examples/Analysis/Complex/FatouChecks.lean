/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Nontangential.Limit
public import TauCeti.Analysis.Complex.UpperHalfPlane.Poisson.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Checks for boundary limits of Poisson integrals on the half-plane

The first two Checks of Fatou's theorem for Poisson integrals
(DiracScatteringAndNonlinearFourierTransform roadmap §2.4), computed directly.

* *A Dirac mass.* For `ν = δ₀`, `P[δ₀](z) = Im z / (π |z|²) → 0` as `z → x` for every `x ≠ 0`,
  without restriction on the approach, in particular nontangentially
  (`tendsto_poissonIntegral_dirac`,
  `tendsto_nontangentialFilter_poissonIntegral_dirac`), and the density `w` of the absolutely
  continuous part of `δ₀` vanishes (`rnDeriv_dirac_ae_eq_zero`).
* *An indicator.* For `h = 1_{[0, 1]}`, read as the measure `volume.restrict [0, 1]`,
  `P[h](x + iy) = (arctan ((1 - x) / y) + arctan (x / y)) / π`
  (`poissonIntegral_indicator_Icc`). As `z → x` through the upper half-plane, `P[h](z) → 1` for
  `0 < x < 1` and `P[h](z) → 0` for `x < 0` and for `x > 1`
  (`tendsto_poissonIntegral_indicator_Icc_one`, `tendsto_poissonIntegral_indicator_Icc_zero_of_neg`,
  `tendsto_poissonIntegral_indicator_Icc_zero_of_one_lt`). At the jump `x = 0` there is no
  nontangential limit: `P[h](iy) → 1/2` while `P[h](-y/2 + iy) → 1/2 - arctan (1/2) / π`
  (`not_tendsto_nontangentialFilter_poissonIntegral_indicator_Icc`).
-/

public section

noncomputable section

namespace TauCeti.Examples.Fatou

open Complex Filter MeasureTheory Set Topology

open scoped Real

/-- The Poisson kernel in real coordinates: `P(z, s) = Im z / (π ((s - Re z)² + (Im z)²))`. -/
theorem upperHalfPlanePoissonKernel_eq_div (z : ℂ) (s : ℝ) :
    upperHalfPlanePoissonKernel z s = z.im / (π * ((s - z.re) ^ 2 + z.im ^ 2)) := by
  rw [upperHalfPlanePoissonKernel_eq, normSq_apply]
  simp only [sub_re, ofReal_re, sub_im, ofReal_im, zero_sub]
  ring

/-! ### A Dirac mass -/

/-- **`P[δ₀](z) → 0` as `z → x ≠ 0`**, from any direction. -/
theorem tendsto_poissonIntegral_dirac {x : ℝ} (hx : x ≠ 0) :
    Tendsto (upperHalfPlanePoissonIntegral (Measure.dirac 0)) (𝓝 (x : ℂ)) (𝓝 0) := by
  have hden : π * (((0 : ℝ) - (x : ℂ).re) ^ 2 + (x : ℂ).im ^ 2) ≠ 0 := by
    simp [Real.pi_ne_zero, hx]
  have hc : ContinuousAt (fun z : ℂ => z.im / (π * (((0 : ℝ) - z.re) ^ 2 + z.im ^ 2)))
      (x : ℂ) :=
    continuous_im.continuousAt.div (by fun_prop) hden
  have := hc.tendsto
  simp only [ofReal_im, zero_div] at this
  refine this.congr fun z => ?_
  rw [upperHalfPlanePoissonIntegral_dirac, upperHalfPlanePoissonKernel_eq_div]

/-- In particular `P[δ₀]` has nontangential limit `0` at every `x ≠ 0`. -/
theorem tendsto_nontangentialFilter_poissonIntegral_dirac {x : ℝ} (hx : x ≠ 0) (α : ℝ) :
    Tendsto (upperHalfPlanePoissonIntegral (Measure.dirac 0)) (nontangentialFilter α x)
      (𝓝 0) :=
  (tendsto_poissonIntegral_dirac hx).mono_left (by
    rw [nontangentialFilter_def]
    exact nhdsWithin_le_nhds)

/-- The absolutely continuous part of `δ₀` has density `w = 0`. -/
theorem rnDeriv_dirac_ae_eq_zero :
    (Measure.dirac (0 : ℝ)).rnDeriv volume =ᵐ[volume] 0 :=
  (Measure.rnDeriv_eq_zero _ _).2 (mutuallySingular_dirac 0 volume)

/-! ### The indicator of `[0, 1]` -/

/-- **The Poisson integral of `1_{[0, 1]}`**: for `Im z > 0`,
`P[1_{[0,1]}](z) = (arctan ((1 - Re z) / Im z) + arctan (Re z / Im z)) / π`. -/
theorem poissonIntegral_indicator_Icc {z : ℂ} (hz : 0 < z.im) :
    upperHalfPlanePoissonIntegral (volume.restrict (Icc 0 1)) z =
      (Real.arctan ((1 - z.re) / z.im) + Real.arctan (z.re / z.im)) / π := by
  have hP : upperHalfPlanePoissonKernel z =
      fun s : ℝ => z.im / (π * ((s - z.re) ^ 2 + z.im ^ 2)) :=
    funext (upperHalfPlanePoissonKernel_eq_div z)
  have hcont : Continuous (upperHalfPlanePoissonKernel z) := by
    rw [hP]
    exact continuous_const.div (by fun_prop) fun s => by positivity
  have hderiv (s : ℝ) : HasDerivAt (fun s => Real.arctan ((s - z.re) / z.im) / π)
      (upperHalfPlanePoissonKernel z s) s := by
    have h : HasDerivAt (fun s => Real.arctan ((s - z.re) / z.im) / π)
        (1 / (1 + ((s - z.re) / z.im) ^ 2) * (1 / z.im) / π) s :=
      ((Real.hasDerivAt_arctan _).comp s
        (((hasDerivAt_id' s).sub_const z.re).div_const z.im)).div_const π
    convert h using 1
    rw [upperHalfPlanePoissonKernel_eq_div]
    field_simp
    ring
  rw [upperHalfPlanePoissonIntegral_def, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s)
      (hcont.intervalIntegrable 0 1)]
  rw [zero_sub, neg_div, Real.arctan_neg]
  ring

/-- The filter of approach to `x` through the upper half-plane. -/
abbrev upperNhds (x : ℝ) : Filter ℂ :=
  𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)

/-- Along the approach through the upper half-plane, `Im z → 0⁺`. -/
theorem tendsto_im_upperNhds (x : ℝ) : Tendsto im (upperNhds x) (𝓝[>] 0) :=
  tendsto_nhdsWithin_iff.2 ⟨(continuous_im.tendsto' _ 0 (by simp)).mono_left nhdsWithin_le_nhds,
    eventually_nhdsWithin_of_forall fun _ hz => hz⟩

/-- Along the approach to `x` through the upper half-plane, `Re z → x`. -/
theorem tendsto_re_upperNhds (x : ℝ) : Tendsto re (upperNhds x) (𝓝 x) :=
  (continuous_re.tendsto' _ x (by simp)).mono_left nhdsWithin_le_nhds

/-- If `f → c > 0` along the approach to `x`, then `arctan (f z / Im z) → π / 2`. -/
theorem tendsto_arctan_div_im_of_pos {x : ℝ} {f : ℂ → ℝ} {c : ℝ} (hc : 0 < c)
    (hf : Tendsto f (upperNhds x) (𝓝 c)) :
    Tendsto (fun z => Real.arctan (f z / z.im)) (upperNhds x) (𝓝 (π / 2)) := by
  refine (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp ?_
  simp_rw [div_eq_mul_inv]
  exact hf.pos_mul_atTop hc (tendsto_inv_nhdsGT_zero.comp (tendsto_im_upperNhds x))

/-- If `f → c < 0` along the approach to `x`, then `arctan (f z / Im z) → -π / 2`. -/
theorem tendsto_arctan_div_im_of_neg {x : ℝ} {f : ℂ → ℝ} {c : ℝ} (hc : c < 0)
    (hf : Tendsto f (upperNhds x) (𝓝 c)) :
    Tendsto (fun z => Real.arctan (f z / z.im)) (upperNhds x) (𝓝 (-(π / 2))) := by
  refine (Real.tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp ?_
  simp_rw [div_eq_mul_inv]
  exact hf.neg_mul_atTop hc (tendsto_inv_nhdsGT_zero.comp (tendsto_im_upperNhds x))

/-- Along the approach through the upper half-plane, `P[1_{[0,1]}]` agrees with its arctan
formula. -/
theorem poissonIntegral_indicator_Icc_eventuallyEq (x : ℝ) :
    upperHalfPlanePoissonIntegral (volume.restrict (Icc 0 1)) =ᶠ[upperNhds x]
      fun z => (Real.arctan ((1 - z.re) / z.im) + Real.arctan (z.re / z.im)) / π :=
  eventually_nhdsWithin_of_forall fun _ hz => poissonIntegral_indicator_Icc hz

/-- **Inside the interval the boundary limit is `1`**: for `0 < x < 1`, `P[1_{[0,1]}](z) → 1` as
`z → x` through the upper half-plane. -/
theorem tendsto_poissonIntegral_indicator_Icc_one {x : ℝ} (hx : x ∈ Ioo 0 1) :
    Tendsto (upperHalfPlanePoissonIntegral (volume.restrict (Icc 0 1))) (upperNhds x) (𝓝 1) := by
  have h₁ := tendsto_arctan_div_im_of_pos (sub_pos.2 hx.2)
    (tendsto_const_nhds.sub (tendsto_re_upperNhds x))
  have h₂ := tendsto_arctan_div_im_of_pos hx.1 (tendsto_re_upperNhds x)
  have := (h₁.add h₂).div_const π
  rw [add_halves, div_self Real.pi_ne_zero] at this
  exact this.congr' (poissonIntegral_indicator_Icc_eventuallyEq x).symm

/-- **Left of the interval the boundary limit is `0`.** -/
theorem tendsto_poissonIntegral_indicator_Icc_zero_of_neg {x : ℝ} (hx : x < 0) :
    Tendsto (upperHalfPlanePoissonIntegral (volume.restrict (Icc 0 1))) (upperNhds x) (𝓝 0) := by
  have h₁ := tendsto_arctan_div_im_of_pos (by linarith : (0 : ℝ) < 1 - x)
    (tendsto_const_nhds.sub (tendsto_re_upperNhds x))
  have h₂ := tendsto_arctan_div_im_of_neg hx (tendsto_re_upperNhds x)
  have := (h₁.add h₂).div_const π
  rw [add_neg_cancel, zero_div] at this
  exact this.congr' (poissonIntegral_indicator_Icc_eventuallyEq x).symm

/-- **Right of the interval the boundary limit is `0`.** -/
theorem tendsto_poissonIntegral_indicator_Icc_zero_of_one_lt {x : ℝ} (hx : 1 < x) :
    Tendsto (upperHalfPlanePoissonIntegral (volume.restrict (Icc 0 1))) (upperNhds x) (𝓝 0) := by
  have h₁ := tendsto_arctan_div_im_of_neg (sub_neg.2 hx)
    (tendsto_const_nhds.sub (tendsto_re_upperNhds x))
  have h₂ := tendsto_arctan_div_im_of_pos (by linarith : (0 : ℝ) < x) (tendsto_re_upperNhds x)
  have := (h₁.add h₂).div_const π
  rw [neg_add_cancel, zero_div] at this
  exact this.congr' (poissonIntegral_indicator_Icc_eventuallyEq x).symm

/-- The slanted approach `-t/2 + it` to `0`, `t → 0⁺`, is nontangential. -/
theorem tendsto_slanted_nontangentialFilter :
    Tendsto (fun t : ℝ => ((-(t / 2) : ℝ) : ℂ) + t * I) (𝓝[>] 0) (nontangentialFilter 1 0) := by
  rw [nontangentialFilter_def]
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have : Tendsto (fun t : ℝ => ((-(t / 2) : ℝ) : ℂ) + t * I) (𝓝 0)
        (𝓝 (((-((0 : ℝ) / 2) : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I)) :=
      ((by fun_prop : Continuous fun t : ℝ => ((-(t / 2) : ℝ) : ℂ) + t * I).tendsto 0)
    simpa using this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [mem_nontangentialCone]
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, mul_one, sub_zero,
      add_im, mul_im, zero_add, add_zero, one_mul]
    refine ⟨ht, ?_, by simp⟩
    rw [abs_neg, abs_of_pos (by positivity)]
    linarith

/-- **At the jump `x = 0` there is no nontangential limit**: `P[1_{[0,1]}](it) → 1/2` and
`P[1_{[0,1]}](-t/2 + it) → 1/2 - arctan (1/2) / π` as `t → 0⁺`, and both approaches are
nontangential. -/
theorem not_tendsto_nontangentialFilter_poissonIntegral_indicator_Icc (L : ℝ) :
    Tendsto (fun t : ℝ => upperHalfPlanePoissonIntegral (volume.restrict (Icc 0 1)) (t * I))
        (𝓝[>] 0) (𝓝 (1 / 2)) ∧
      Tendsto (fun t : ℝ => upperHalfPlanePoissonIntegral (volume.restrict (Icc 0 1))
          (((-(t / 2) : ℝ) : ℂ) + t * I)) (𝓝[>] 0) (𝓝 (1 / 2 - Real.arctan (1 / 2) / π)) ∧
      ¬Tendsto (upperHalfPlanePoissonIntegral (volume.restrict (Icc 0 1)))
        (nontangentialFilter 1 0) (𝓝 L) := by
  have hinv : Tendsto (fun t : ℝ => t⁻¹) (𝓝[>] 0) atTop := tendsto_inv_nhdsGT_zero
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have hv : Tendsto (fun t : ℝ => upperHalfPlanePoissonIntegral (volume.restrict (Icc 0 1))
      (t * I)) (𝓝[>] 0) (𝓝 (1 / 2)) := by
    have h := ((Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp hinv).div_const π
    have hπ : π / 2 / π = 1 / 2 := by field_simp
    rw [hπ] at h
    refine h.congr' ?_
    filter_upwards [hpos] with t ht
    rw [poissonIntegral_indicator_Icc (by simpa using ht)]
    simp [Function.comp_apply, one_div]
  have hs : Tendsto (fun t : ℝ => upperHalfPlanePoissonIntegral (volume.restrict (Icc 0 1))
      (((-(t / 2) : ℝ) : ℂ) + t * I)) (𝓝[>] 0) (𝓝 (1 / 2 - Real.arctan (1 / 2) / π)) := by
    have h₁ : Tendsto (fun t : ℝ => Real.arctan (t⁻¹ + 1 / 2)) (𝓝[>] 0) (𝓝 (π / 2)) :=
      (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
        (tendsto_atTop_add_const_right _ _ hinv)
    have h := (h₁.add_const (-Real.arctan (1 / 2))).div_const π
    have he : (π / 2 + -Real.arctan (1 / 2)) / π = 1 / 2 - Real.arctan (1 / 2) / π := by
      field_simp
      ring
    rw [he] at h
    refine h.congr' ?_
    filter_upwards [hpos] with t ht
    rw [poissonIntegral_indicator_Icc (by simpa using ht)]
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, mul_one, sub_zero,
      add_im, mul_im, zero_add, add_zero]
    congr 2
    · congr 1
      field_simp
      ring
    · rw [show -(t / 2) / t = -(1 / 2) by field_simp, Real.arctan_neg]
  refine ⟨hv, hs, fun hL => ?_⟩
  have h₁ := tendsto_nhds_unique hv
    (by simpa only [Function.comp_def, ofReal_zero, zero_add] using
      hL.comp (tendsto_vertical_nontangentialFilter one_pos 0))
  have h₂ := tendsto_nhds_unique hs (hL.comp tendsto_slanted_nontangentialFilter)
  have : Real.arctan (1 / 2) = Real.arctan 0 := by
    rw [Real.arctan_zero]
    have := h₁.trans h₂.symm
    field_simp at this
    linarith
  exact one_half_pos.ne' (Real.arctan_injective this)

end TauCeti.Examples.Fatou
