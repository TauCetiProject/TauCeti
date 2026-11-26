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
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Arctan
import TauCeti.Basic.Complex.OfRealSub

/-!
# Checks for boundary limits of Poisson integrals on the half-plane

Explicit examples of Fatou's theorem on boundary limits of Poisson integrals on the upper
half-plane, computed directly.

* *A Dirac mass.* For `ν = δ₀`, `P[δ₀](z) = Im z / (π |z|²) → 0` as `z → x` for every `x ≠ 0`,
  without restriction on the approach, in particular nontangentially
  (`tendsto_upperHalfPlanePoissonIntegral_dirac`,
  `tendsto_nontangentialFilter_upperHalfPlanePoissonIntegral_dirac`), and the density `w` of the
  absolutely continuous part of `δ₀` vanishes (`rnDeriv_dirac_ae_eq_zero`).
* *An indicator.* For `h = 1_{[0, 1]}`, read as the measure `volume.restrict [0, 1]`,
  `P[h](x + iy) = (arctan ((1 - x) / y) + arctan (x / y)) / π`
  (`upperHalfPlanePoissonIntegral_volume_restrict_Icc_zero_one`). As `z → x` through the upper
  half-plane, `P[h](z) → 1` for `0 < x < 1` and `P[h](z) → 0` for `x < 0` and for `x > 1`
  (`tendsto_upperHalfPlanePoissonIntegral_volume_restrict_Icc_zero_one_of_mem_Ioo`,
  `tendsto_upperHalfPlanePoissonIntegral_volume_restrict_Icc_zero_one_of_neg`,
  `tendsto_upperHalfPlanePoissonIntegral_volume_restrict_Icc_zero_one_of_one_lt`). At the jump
  `x = 0`, `P[h](ct + it) → 1/2 + arctan c / π` as `t → 0⁺`
  (`tendsto_upperHalfPlanePoissonIntegral_volume_restrict_Icc_zero_one_ray`), in particular
  `P[h](it) → 1/2` (`tendsto_upperHalfPlanePoissonIntegral_volume_restrict_Icc_zero_one_vertical`).
  The rays with `|c| < α` are nontangential, so there is no nontangential limit at `0` for any
  aperture `α > 0`
  (`not_tendsto_nontangentialFilter_upperHalfPlanePoissonIntegral_volume_restrict_Icc_zero_one`).
-/

public section

noncomputable section

namespace TauCeti.Examples.Fatou

open Complex Filter MeasureTheory Set Topology
open _root_.UpperHalfPlane (upperHalfPlaneSet)

open scoped Real

/-! ### A Dirac mass -/

/-- **`P[δ₀](z) → 0` as `z → x ≠ 0`**, from any direction. -/
theorem tendsto_upperHalfPlanePoissonIntegral_dirac {x : ℝ} (hx : x ≠ 0) :
    Tendsto (upperHalfPlanePoissonIntegral (Measure.dirac 0)) (𝓝 (x : ℂ)) (𝓝 0) := by
  have hden : π * (((0 : ℝ) - (x : ℂ).re) ^ 2 + (x : ℂ).im ^ 2) ≠ 0 := by
    simp [Real.pi_ne_zero, hx]
  have hc : ContinuousAt (fun z : ℂ => z.im / (π * (((0 : ℝ) - z.re) ^ 2 + z.im ^ 2)))
      (x : ℂ) :=
    continuous_im.continuousAt.div (by fun_prop) hden
  have := hc.tendsto
  simp only [ofReal_im, zero_div] at this
  refine this.congr fun z => ?_
  rw [upperHalfPlanePoissonIntegral_dirac, upperHalfPlanePoissonKernel_eq, normSq_ofReal_sub]

/-- In particular `P[δ₀]` has nontangential limit `0` at every `x ≠ 0`. -/
theorem tendsto_nontangentialFilter_upperHalfPlanePoissonIntegral_dirac {x : ℝ} (hx : x ≠ 0)
    (α : ℝ) :
    Tendsto (upperHalfPlanePoissonIntegral (Measure.dirac 0)) (nontangentialFilter α x)
      (𝓝 0) :=
  (tendsto_upperHalfPlanePoissonIntegral_dirac hx).mono_left (by
    rw [nontangentialFilter_def]
    exact nhdsWithin_le_nhds)

/-- The absolutely continuous part of `δ₀` has density `w = 0`. -/
theorem rnDeriv_dirac_ae_eq_zero :
    (Measure.dirac (0 : ℝ)).rnDeriv volume =ᵐ[volume] 0 :=
  (Measure.rnDeriv_eq_zero _ _).2 (mutuallySingular_dirac 0 volume)

/-! ### The indicator of `[0, 1]` -/

/-- **The Poisson integral of `1_{[0, 1]}`**:
`P[1_{[0,1]}](z) = (arctan ((1 - Re z) / Im z) + arctan (Re z / Im z)) / π`. -/
theorem upperHalfPlanePoissonIntegral_volume_restrict_Icc_zero_one (z : ℂ) :
    upperHalfPlanePoissonIntegral (volume.restrict (Icc 0 1)) z =
      (Real.arctan ((1 - z.re) / z.im) + Real.arctan (z.re / z.im)) / π := by
  rw [upperHalfPlanePoissonIntegral_volume_restrict_Icc zero_le_one, zero_sub, neg_div,
    Real.arctan_neg, sub_neg_eq_add]

/-- **Inside the interval the boundary limit is `1`**: for `0 < x < 1`, `P[1_{[0,1]}](z) → 1` as
`z → x` through the upper half-plane. -/
theorem tendsto_upperHalfPlanePoissonIntegral_volume_restrict_Icc_zero_one_of_mem_Ioo {x : ℝ}
    (hx : x ∈ Ioo 0 1) :
    Tendsto (upperHalfPlanePoissonIntegral (volume.restrict (Icc 0 1)))
      (𝓝[upperHalfPlaneSet] (x : ℂ)) (𝓝 1) := by
  simpa [Real.sign_of_pos (sub_pos.2 hx.2), Real.sign_of_neg (neg_neg_of_pos hx.1)] using
    tendsto_upperHalfPlanePoissonIntegral_volume_restrict_Icc zero_le_one hx.1.ne' hx.2.ne

/-- **Left of the interval the boundary limit is `0`.** -/
theorem tendsto_upperHalfPlanePoissonIntegral_volume_restrict_Icc_zero_one_of_neg {x : ℝ}
    (hx : x < 0) :
    Tendsto (upperHalfPlanePoissonIntegral (volume.restrict (Icc 0 1)))
      (𝓝[upperHalfPlaneSet] (x : ℂ)) (𝓝 0) := by
  simpa [Real.sign_of_pos (by linarith : (0 : ℝ) < 1 - x), Real.sign_of_pos (neg_pos.2 hx)] using
    tendsto_upperHalfPlanePoissonIntegral_volume_restrict_Icc zero_le_one hx.ne (by linarith)

/-- **Right of the interval the boundary limit is `0`.** -/
theorem tendsto_upperHalfPlanePoissonIntegral_volume_restrict_Icc_zero_one_of_one_lt {x : ℝ}
    (hx : 1 < x) :
    Tendsto (upperHalfPlanePoissonIntegral (volume.restrict (Icc 0 1)))
      (𝓝[upperHalfPlaneSet] (x : ℂ)) (𝓝 0) := by
  simpa [Real.sign_of_neg (sub_neg.2 hx), Real.sign_of_neg (by linarith : -x < 0)] using
    tendsto_upperHalfPlanePoissonIntegral_volume_restrict_Icc zero_le_one (by linarith) hx.ne'

/-- **Limits at the jump along rays**: `P[1_{[0,1]}](ct + it) → 1/2 + arctan c / π` as
`t → 0⁺`. -/
theorem tendsto_upperHalfPlanePoissonIntegral_volume_restrict_Icc_zero_one_ray (c : ℝ) :
    Tendsto (fun t : ℝ => upperHalfPlanePoissonIntegral (volume.restrict (Icc 0 1))
      (((c * t : ℝ) : ℂ) + t * I)) (𝓝[>] 0) (𝓝 (1 / 2 + Real.arctan c / π)) := by
  have h₁ : Tendsto (fun t : ℝ => Real.arctan ((1 - c * t) / t)) (𝓝[>] 0) (𝓝 (π / 2)) := by
    have hf : Tendsto (fun t : ℝ => 1 - c * t) (𝓝[>] 0) (𝓝 1) :=
      ((by fun_prop : Continuous fun t : ℝ => 1 - c * t).tendsto' 0 1 (by simp)).mono_left
        nhdsWithin_le_nhds
    simpa using Real.tendsto_arctan_div_of_tendsto_nhdsGT_zero hf one_ne_zero tendsto_id
  have h := (h₁.add_const (Real.arctan c)).div_const π
  have he : (π / 2 + Real.arctan c) / π = 1 / 2 + Real.arctan c / π := by
    field_simp
  rw [he] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  rw [upperHalfPlanePoissonIntegral_volume_restrict_Icc_zero_one]
  simp [mul_div_cancel_right₀ c ht.ne']

/-- **The vertical limit at the jump**: `P[1_{[0,1]}](it) → 1/2` as `t → 0⁺`. -/
theorem tendsto_upperHalfPlanePoissonIntegral_volume_restrict_Icc_zero_one_vertical :
    Tendsto (fun t : ℝ => upperHalfPlanePoissonIntegral (volume.restrict (Icc 0 1)) (t * I))
      (𝓝[>] 0) (𝓝 (1 / 2)) := by
  simpa using tendsto_upperHalfPlanePoissonIntegral_volume_restrict_Icc_zero_one_ray 0

/-- **At the jump `x = 0` there is no nontangential limit**, for any aperture `α > 0`: the rays
`ct + it` with `|c| < α` approach `0` nontangentially, and along them `P[1_{[0,1]}]` tends to the
different values `1/2 + arctan c / π`. -/
theorem not_tendsto_nontangentialFilter_upperHalfPlanePoissonIntegral_volume_restrict_Icc_zero_one
    {α : ℝ} (hα : 0 < α) (L : ℝ) :
    ¬Tendsto (upperHalfPlanePoissonIntegral (volume.restrict (Icc 0 1)))
      (nontangentialFilter α 0) (𝓝 L) := by
  intro hL
  have hray (c : ℝ) (hc : |c| < α) : 1 / 2 + Real.arctan c / π = L :=
    tendsto_nhds_unique (tendsto_upperHalfPlanePoissonIntegral_volume_restrict_Icc_zero_one_ray c)
      (by simpa only [Function.comp_def, zero_add] using
        hL.comp (tendsto_ray_nontangentialFilter hc 0))
  have h := (hray 0 (by simpa using hα)).trans
    (hray (α / 2) (by rw [abs_of_pos (half_pos hα)]; linarith)).symm
  rw [add_right_inj, div_left_inj₀ Real.pi_ne_zero] at h
  exact (half_pos hα).ne (Real.arctan_injective h)

end TauCeti.Examples.Fatou
