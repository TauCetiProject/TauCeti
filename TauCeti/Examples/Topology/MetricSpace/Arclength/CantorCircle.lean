/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.CantorFunction
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.MeasureTheory.Integral.CircleIntegral
import TauCeti.MeasureTheory.Function.AreaFormula.Circle

/-!
# A circle traversed along the Cantor function

Let `C` be the Cantor–Lebesgue function and `φ(t) = (t + C(t)) / 2` (`cantorTime`), a strictly
increasing continuous map of `[0, 1]` onto itself. It is not absolutely continuous: `φ' = 1/2` at
almost every point (`ae_hasDerivAt_cantorTime`), so `∫₀¹ φ' = 1/2`, while `φ(1) − φ(0) = 1`
(`integral_deriv_cantorTime`).

The curve `γ(t) = exp(2πi φ(t))` (`cantorCircle`) is closed and injective on `[0, 1)`
(`cantorCircle_zero`, `cantorCircle_one`, `injOn_cantorCircle`), and has length `2π`
(`eVariationOn_cantorCircle`), since variation is invariant under monotone reparametrization.
Almost everywhere `‖γ'(t)‖ = 2π φ'(t) = π` (`ae_norm_deriv_cantorCircle`), so
`∫₀¹ ‖γ'‖ = π ≠ 2π` (`integral_norm_deriv_cantorCircle`): the length formula
`length = ∫ ‖γ'‖` needs absolute continuity.

This is the first Check of §1.1 of `TauCetiRoadmap/GeometricMeasureTheory/README.md`.
-/

@[expose] public section

noncomputable section

open Real Set MeasureTheory

namespace TauCeti.Examples.CantorCircle

/-- The reparametrization `φ(t) = (t + C(t)) / 2`, with `C` the Cantor–Lebesgue function. -/
def cantorTime (t : ℝ) : ℝ := (t + cantorFunction t) / 2

theorem strictMono_cantorTime : StrictMono cantorTime := fun a b h => by
  have := monotone_cantorFunction h.le
  simp only [cantorTime]
  linarith

theorem continuous_cantorTime : Continuous cantorTime :=
  (continuous_id.add continuous_cantorFunction).div_const 2

@[simp]
theorem cantorTime_zero : cantorTime 0 = 0 := by
  simp [cantorTime]

@[simp]
theorem cantorTime_one : cantorTime 1 = 1 := by
  norm_num [cantorTime, cantorFunction_one]

/-- `φ` maps `[0, 1]` onto itself. -/
theorem image_cantorTime_Icc : cantorTime '' Icc 0 1 = Icc 0 1 := by
  rw [continuous_cantorTime.continuousOn.image_Icc_of_monotoneOn zero_le_one
    (strictMono_cantorTime.monotone.monotoneOn _), cantorTime_zero, cantorTime_one]

/-- Off the Cantor set, `φ' = 1/2`. -/
theorem hasDerivAt_cantorTime_of_notMem {t : ℝ} (ht : t ∉ cantorSet) :
    HasDerivAt cantorTime (1 / 2) t := by
  convert ((hasDerivAt_id t).add (hasDerivAt_cantorFunction_of_notMem ht)).div_const 2 using 1
  · rfl
  · norm_num

/-- `φ' = 1/2` at almost every point. -/
theorem ae_hasDerivAt_cantorTime : ∀ᵐ t, HasDerivAt cantorTime (1 / 2) t :=
  (measure_eq_zero_iff_ae_notMem.mp volume_cantorSet).mono
    fun _ => hasDerivAt_cantorTime_of_notMem

/-- `φ` is not absolutely continuous: `∫₀¹ φ' = 1/2`, while `φ(1) − φ(0) = 1`. -/
theorem integral_deriv_cantorTime :
    ∫ t in (0 : ℝ)..1, deriv cantorTime t = 1 / 2 ∧ cantorTime 1 - cantorTime 0 = 1 := by
  refine ⟨?_, by simp⟩
  rw [intervalIntegral.integral_congr_ae (g := fun _ => (1 / 2 : ℝ))
    (ae_hasDerivAt_cantorTime.mono fun t ht _ => ht.deriv)]
  simp

/-- The circle `γ(t) = exp(2πi φ(t))` traversed along the Cantor function. -/
def cantorCircle (t : ℝ) : ℂ := circleMap 0 1 (2 * π * cantorTime t)

@[simp]
theorem cantorCircle_zero : cantorCircle 0 = 1 := by
  simp [cantorCircle, circleMap]

@[simp]
theorem cantorCircle_one : cantorCircle 1 = 1 := by
  simp [cantorCircle, circleMap, Complex.exp_two_pi_mul_I]

/-- `γ` is injective on `[0, 1)`. -/
theorem injOn_cantorCircle : InjOn cantorCircle (Ico 0 1) := by
  have hmap : MapsTo (fun t => 2 * π * cantorTime t) (Ico 0 1) (Ico 0 (2 * π)) := by
    intro t ht
    have h0 := strictMono_cantorTime.monotone ht.1
    have h1 := strictMono_cantorTime ht.2
    rw [cantorTime_zero] at h0
    rw [cantorTime_one] at h1
    exact ⟨by positivity, by nlinarith [pi_pos]⟩
  have hc : InjOn (circleMap 0 1) (Ico 0 (2 * π)) :=
    injOn_circleMap_of_abs_sub_le' one_ne_zero (by simp)
  have hg : StrictMono fun t => 2 * π * cantorTime t := fun a b h =>
    mul_lt_mul_of_pos_left (strictMono_cantorTime h) (by positivity)
  exact hc.comp hg.injective.injOn hmap

/-- **Length of `γ`.** The curve has length `2π`: variation is invariant under the monotone
reparametrization `t ↦ 2π φ(t)` of `[0, 1]` onto `[0, 2π]`. -/
theorem eVariationOn_cantorCircle :
    eVariationOn cantorCircle (Icc 0 1) = ENNReal.ofReal (2 * π) := by
  have hmono : MonotoneOn (fun t => 2 * π * cantorTime t) (Icc 0 1) := fun a _ b _ h =>
    mul_le_mul_of_nonneg_left (strictMono_cantorTime.monotone h) (by positivity)
  have himage : (fun t => 2 * π * cantorTime t) '' Icc 0 1 = Icc 0 (2 * π) := by
    rw [← image_image (fun s => 2 * π * s) cantorTime, image_cantorTime_Icc,
      image_mul_left_Icc (by positivity) zero_le_one, mul_zero, mul_one]
  rw [show cantorCircle = circleMap 0 1 ∘ fun t => 2 * π * cantorTime t from rfl,
    eVariationOn.comp_eq_of_monotoneOn _ _ hmono, himage, eVariationOn_circleMap_Icc_zero_two_pi,
    abs_one, Complex.euclideanHausdorffMeasure_sphere, mul_one]

/-- Off the Cantor set, `γ' = π i γ`. -/
theorem hasDerivAt_cantorCircle_of_notMem {t : ℝ} (ht : t ∉ cantorSet) :
    HasDerivAt cantorCircle ((2 * π * (1 / 2) : ℝ) • (circleMap 0 1 (2 * π * cantorTime t) *
      Complex.I)) t :=
  (hasDerivAt_circleMap 0 1 _).scomp t ((hasDerivAt_cantorTime_of_notMem ht).const_mul (2 * π))

/-- `‖γ'(t)‖ = 2π φ'(t) = π` at almost every `t`. -/
theorem ae_norm_deriv_cantorCircle : ∀ᵐ t, ‖deriv cantorCircle t‖ = π :=
  (measure_eq_zero_iff_ae_notMem.mp volume_cantorSet).mono fun t ht => by
    rw [(hasDerivAt_cantorCircle_of_notMem ht).deriv, norm_smul, norm_mul (circleMap 0 1 _),
      norm_circleMap_zero,
      Complex.norm_I, abs_one, mul_one, mul_one, Real.norm_eq_abs, abs_of_pos (by positivity)]
    ring

/-- **The length formula fails.** `∫₀¹ ‖γ'‖ = π`, half the length `2π` of `γ`. -/
theorem integral_norm_deriv_cantorCircle : ∫ t in (0 : ℝ)..1, ‖deriv cantorCircle t‖ = π := by
  rw [intervalIntegral.integral_congr_ae (g := fun _ => π)
    (ae_norm_deriv_cantorCircle.mono fun t ht _ => ht)]
  simp

end TauCeti.Examples.CantorCircle
